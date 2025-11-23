/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.RingTheory.Bialgebra.Basic

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

/-- The comultiplication is the unique algebra map induced by the map
`x : X => ι R x ⊗ₜ 1 + 1 ⊗ₜ ι R x -/
def comul : (FreeAlgebra R X) →ₐ[R] (FreeAlgebra R X ⊗[R] FreeAlgebra R X) :=
  lift R <| fun m => ι R m ⊗ₜ 1 + 1 ⊗ₜ ι R m

instance instBialgebra : Bialgebra R (FreeAlgebra R X) :=
  Bialgebra.ofAlgHom (comul R X) algebraMapInv
  (by ext; simpa [comul, tmul_add, add_tmul, Algebra.TensorProduct.one_def] using by abel)
  (by ext; simp [comul, algebraMapInv])
  (by ext; simp [comul, algebraMapInv])

end FreeAlgebra
