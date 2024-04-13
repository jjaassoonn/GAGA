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

open AlgebraicGeometry Opposite

local notation "Specℂ" => Scheme.Spec.obj (op <| CommRingCat.of ℂ)

/--
A scheme locally of finite type over complex numbers is a scheme over ℂ such that the structure
morphism is locally of finite type.
-/
structure SchemeLocallyOfFiniteTypeOverComplex extends Scheme :=
toSpecℂ : toScheme ⟶ Specℂ
locally_finite : LocallyOfFiniteType toSpecℂ
