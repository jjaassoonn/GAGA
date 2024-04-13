/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Data.Complex.Basic

/-!
# Scheme locally of finite type over complex numbers

-/

open AlgebraicGeometry Opposite CategoryTheory

local notation "Specℂ" => Scheme.Spec.obj (op <| CommRingCat.of ℂ)

/--
A scheme locally of finite type over complex numbers is a scheme over ℂ such that the structure
morphism is locally of finite type.
-/
structure SchemeLocallyOfFiniteTypeOverComplex extends Scheme :=
toSpecℂ : toScheme ⟶ Specℂ
[locally_finite : LocallyOfFiniteType toSpecℂ]


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

end SchemeLocallyOfFiniteTypeOverComplex
