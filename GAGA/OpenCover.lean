import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme

open Opposite

namespace AlgebraicGeometry.Scheme

/--
Open cover of a scheme by all of its affine opens.
-/
@[simps]
noncomputable def openCoverOfAllAffineOpens (X : Scheme) : OpenCover X where
  J := X.affineOpens
  obj U := X ∣_ᵤ U
  map _ := X.ofRestrict _
  f x :=
    let U := X.local_affine x |>.choose.1
    let R := X.local_affine x |>.choose_spec.choose
    let i : X ∣_ᵤ U ≅ Spec.obj (op R) :=
    { hom := X.local_affine x |>.choose_spec.choose_spec.some.hom
      inv := X.local_affine x |>.choose_spec.choose_spec.some.inv
      hom_inv_id := X.local_affine x |>.choose_spec.choose_spec.some.hom_inv_id
      inv_hom_id := X.local_affine x |>.choose_spec.choose_spec.some.inv_hom_id }
    ⟨U, isAffineOfIso i.hom⟩
  Covers x := ⟨⟨x, X.local_affine x |>.choose.2⟩, rfl⟩
  IsOpen _ := inferInstance

instance inst_isAffine_of_openCoverOfAllAffineOpens (X : Scheme) (U) :
    IsAffine (X.openCoverOfAllAffineOpens.obj U) := U.2

end AlgebraicGeometry.Scheme
