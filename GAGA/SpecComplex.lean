import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Data.Complex.Basic

open AlgebraicGeometry Opposite CategoryTheory TopologicalSpace

namespace SpecComplex

scoped notation "Specℂ" => Scheme.Spec.obj (op <| CommRingCat.of ℂ)

/--
the open cover of `Spec ℂ` by the single open set `Spec ℂ`.
-/
@[simps]
protected noncomputable def openCover : Scheme.OpenCover Specℂ where
  J := PUnit
  obj _ := Specℂ
  map _ := 𝟙 _
  f _ := ⟨⟩
  Covers := by aesop

instance isnt_openCover_isAffine (i) : IsAffine (SpecComplex.openCover.obj i) :=
  inferInstanceAs <| IsAffine Specℂ

end SpecComplex
