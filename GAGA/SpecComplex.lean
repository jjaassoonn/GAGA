import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Data.Complex.Basic

open AlgebraicGeometry Opposite CategoryTheory TopologicalSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

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

instance : Unique Specℂ where
  default := ⟨⊥, show Ideal.IsPrime (⊥ : Ideal ℂ) from Ideal.bot_prime⟩
  uniq 𝔭 := PrimeSpectrum.ext _ _ <|
    (Ring.isField_iff_isSimpleOrder_ideal.mp <| Field.toIsField ℂ).2 𝔭.asIdeal |>.elim id
      fun r ↦ (𝔭.2.1 r).elim

instance : IsSimpleOrder (Opens Specℂ) where
  exists_pair_ne := ⟨⊥, ⊤, by aesop⟩
  eq_bot_or_eq_top U := by
    by_cases h : (default : Specℂ) ∈ U
    · right
      rw [eq_top_iff]
      rintro x -
      rwa [Unique.eq_default x]
    · left
      rw [eq_bot_iff]
      rintro x h'
      rw [Unique.eq_default x] at h'
      exact h h'
end SpecComplex
