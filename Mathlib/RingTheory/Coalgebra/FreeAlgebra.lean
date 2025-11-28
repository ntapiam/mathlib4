/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.RingTheory.Bialgebra.FreeAlgebra

/-!
Implementation of `Bialgebra` for `FreeAlgebra R X`.
The coproduct is the lift of the map `x : X => ι R x ⊗ₜ 1 + 1 ⊗ₜ ι R x` and `algebraMapInv` acts as
the counit.
-/
@[expose] public section

namespace FreeAlgebra

open scoped TensorProduct
open TensorProduct LinearMap

variable (R X) [CommSemiring R]

instance instCoalgebra : Coalgebra R (FreeAlgebra R X) := Bialgebra.toCoalgebra

end FreeAlgebra
