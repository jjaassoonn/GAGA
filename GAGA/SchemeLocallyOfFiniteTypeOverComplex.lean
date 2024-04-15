/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import GAGA.SpecComplex
import GAGA.OpenCover

/-!
# Scheme locally of finite type over complex numbers

-/

open AlgebraicGeometry Opposite CategoryTheory TopologicalSpace

open SpecComplex

/--
A scheme locally of finite type over complex numbers is a scheme over ℂ such that the structure
morphism is locally of finite type.
-/
structure SchemeLocallyOfFiniteTypeOverComplex extends Scheme :=
toSpecℂ : toScheme ⟶ Specℂ
[locally_finite : LocallyOfFiniteType toSpecℂ]

attribute [instance] SchemeLocallyOfFiniteTypeOverComplex.locally_finite

namespace SchemeLocallyOfFiniteTypeOverComplex

/--
A morphism between two schemes locally of finite type over ℂ, is a morphism of schemes that is
compatible with the structure morphisms.
-/
structure Hom (X Y : SchemeLocallyOfFiniteTypeOverComplex) :=
hom : X.toScheme ⟶ Y.toScheme
commutes : hom ≫ Y.toSpecℂ = X.toSpecℂ := by aesop_cat

attribute [reassoc] Hom.commutes

instance instCategory : Category (SchemeLocallyOfFiniteTypeOverComplex) where
  Hom := Hom
  id X :=
  { hom := 𝟙 X.toScheme }
  comp f g :=
  { hom := f.hom ≫ g.hom
    commutes := by rw [Category.assoc, g.commutes, f.commutes]}

/--
Restriction of a scheme locally of finite type over ℂ to an open set is also locally of finite type.
-/
@[simps toScheme toSpecℂ]
noncomputable def restrict (X : SchemeLocallyOfFiniteTypeOverComplex) (U : Opens X.carrier) :
  SchemeLocallyOfFiniteTypeOverComplex where
toScheme := X.toScheme ∣_ᵤ U
toSpecℂ := X.toScheme.ofRestrict _ ≫ X.toSpecℂ


variable {X : SchemeLocallyOfFiniteTypeOverComplex} (U : Opens X.carrier)
section algebra

noncomputable instance instSectionAlgebra :
    Algebra ℂ (Scheme.Γ.obj (op <| X.restrict U |>.toScheme)) :=
  RingHom.toAlgebra <| RingHom.comp (Scheme.Γ.map (op (X.restrict U).toSpecℂ)) <|
    SpecΓIdentity.inv.app (.of ℂ)


end algebra

variable (X) in
@[simps!]
noncomputable def pullbackSpecℂCover (i) :
    Scheme.OpenCover (SpecComplex.openCover.pullbackCover X.toSpecℂ |>.obj i) :=
  Scheme.Pullback.openCoverOfLeft X.toScheme.openCoverOfAllAffineOpens _ _

instance inst_pullbackSpecℂCover_isAffine (i) (j) :
    IsAffine (X.pullbackSpecℂCover i |>.obj j) :=
  Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _

section affine_open

variable {U} in
/--
Let `X` be a scheme locally of finite type over ℂ and `U` be an affine open set, then the sections
on `U` is a finitely generated `ℂ`-algebra.
-/
lemma sections_finite (hU : IsAffineOpen U) :
    Algebra.FiniteType ℂ (Scheme.Γ.obj (op <| X.restrict U |>.toScheme)) := by
  letI : IsAffine (X.toScheme ∣_ᵤ U) := hU
  have h1 := LocallyOfFiniteType.affine_openCover_iff (X.restrict U).toSpecℂ SpecComplex.openCover
    (fun i => (X.restrict U).pullbackSpecℂCover i) |>.mp (X.restrict U).locally_finite ⟨⟩
    ⟨⊤, show IsAffine <| (X.toScheme.restrict _).restrict _ from ?_⟩
  pick_goal 2
  · refine @isAffineOfIso _ (X.toScheme ∣_ᵤ U) (Scheme.ofRestrict _ _) ?_ _
    refine @IsOpenImmersion.to_iso _ _ _ _ <| ConcreteCategory.epi_of_surjective _ ?_
    rintro ⟨y, hy⟩
    exact ⟨⟨⟨y, hy⟩, ⟨⟩⟩, rfl⟩
  set f := _; change RingHom.FiniteType f at h1
  set g := _; change RingHom.FiniteType g

  suffices eq1 :
    f = RingHom.comp (Scheme.Γ.map <| op <| Limits.pullback.fst ≫ Scheme.ofRestrict _ _)
      (g.comp <| SpecΓIdentity.hom.app (.of ℂ)) by
    set l := _; set r := _; change f = RingHom.comp l (g.comp r) at eq1
    letI iso1 : IsIso (CommRingCat.ofHom l) := by
      refine @CategoryTheory.Functor.map_isIso (F := _) (f := _) (@isIso_op (f := _) <|
        @IsIso.comp_isIso (f := _) (h := _)
          (@Limits.pullback_snd_iso_of_right_iso (f := _) (g := _) ?_) ?_)
      · dsimp; infer_instance
      · refine @IsOpenImmersion.to_iso (f := _) _ (ConcreteCategory.epi_of_surjective _ ?_)
        rintro ⟨y, hy⟩
        exact ⟨⟨⟨y, hy⟩, ⟨⟩⟩, rfl⟩
    letI iso2 : IsIso (CommRingCat.ofHom r) :=
      show IsIso (SpecΓIdentity.hom.app _) from inferInstance
    have eq2 : g =
      RingHom.comp (asIso (f := CommRingCat.ofHom l)).inv
        (f.comp (asIso (f := CommRingCat.ofHom r)).inv) := by
      rw [eq1, RingHom.comp_assoc, RingHom.comp_assoc,
        show RingHom.comp r _ = RingHom.id _ from (asIso (CommRingCat.ofHom r)).inv_hom_id,
        RingHom.comp_id g, ← RingHom.comp_assoc,
        show RingHom.comp _ l = RingHom.id _ from (asIso (CommRingCat.ofHom l)).hom_inv_id,
        RingHom.id_comp g]
    rw [eq2]
    refine RingHom.FiniteType.comp
      (RingHom.FiniteType.of_surjective _ <| Function.Bijective.surjective <|
        ConcreteCategory.bijective_of_isIso (asIso (CommRingCat.ofHom l)).inv)
      (h1.comp <| (RingHom.FiniteType.of_surjective _ <| Function.Bijective.surjective <|
        ConcreteCategory.bijective_of_isIso (asIso (CommRingCat.ofHom r)).inv))

  change Scheme.Γ.map _ = (_ ≫ (SpecΓIdentity.inv.app (CommRingCat.of ℂ) ≫ _)) ≫ _
  conv_rhs => rw [← Category.assoc, ← NatTrans.comp_app, SpecΓIdentity.hom_inv_id,
    NatTrans.id_app]
  erw [Category.id_comp]
  rw [← Scheme.Γ.map_comp]
  change Scheme.Γ.map (op _) = Scheme.Γ.map (op (_ ≫ (X.restrict U).toSpecℂ))
  congr 2
  rw [pullbackSpecℂCover_map]
  erw [Category.assoc]
  dsimp only [restrict_toScheme, restrict_toSpecℂ, Scheme.OpenCover.pullbackCover_obj,
    openCover_obj, openCover_map, Scheme.ofRestrict_val_base, pullbackSpecℂCover_obj, unop_op,
    Scheme.openCoverOfAllAffineOpens_obj, Scheme.openCoverOfAllAffineOpens_map]

  erw [Limits.pullback.lift_snd, Category.comp_id, Limits.pullback.condition, Category.comp_id]

instance inst_sections_finite [hU : Fact <| IsAffineOpen U] :
    Algebra.FiniteType ℂ (Scheme.Γ.obj (op <| X.restrict U |>.toScheme)) :=
  sections_finite hU.out

end affine_open


end SchemeLocallyOfFiniteTypeOverComplex
