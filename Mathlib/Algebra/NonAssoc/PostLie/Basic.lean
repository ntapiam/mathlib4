/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.NonAssoc.PreLie.Basic
/-!
# Post-Lie rings and algebras

In this file we introduce post-Lie rings, defined as a `NonUnitalNonAssocRing` with a `LieRing`
structure satisfying the identities `x * ⁅y, z⁆ = ⁅x * y, z⁆ + ⁅y, x * z⁆` and `⁅x, y⁆ * z =
associator x y z - associator y x z`.

We prove that every `PostLieRing L` is a `LeftPreLieRing L` whenever the bracket vanishes.

Everything holds for the algebra version where `L` is also an `R`-Module over a commutative ring
`R`.

## Main definitions
  * `PostLieRing`
  * `PostLieAlgebra`

## Main results
  * Every `PostLieRing` with vanishing bracket is a `LeftPreLieAlgebra`.

## References
[H. Z. Munthe-Kaas, A. Lundervold, *On Post-Lie Algebras, Lie–Butcher Series and Moving
Frames.*][munthe-kaas_lundervold_2013]
<https://ncatlab.org/nlab/show/post-Lie+algebra>
-/

variable (R L : Type*) [CommRing R]

/-- A `PostLieRing L` is a `NonUnitalNonAssocRing L` with a `LieRing L` structure satisfying two
identities. -/
@[ext]
class PostLieRing extends NonUnitalNonAssocRing L, LieRing L where
  mul_bracket' (x y z : L) : x * ⁅y, z⁆ = ⁅x * y, z⁆ + ⁅y, x * z⁆
  bracket_mul' (x y z : L) : ⁅x, y⁆ * z = associator x y z - associator y x z

/-- A `PostLieAlgebra R L` is a `NonUnitalNonAssocRing L` with a `LieRing L` structure satisfying
twoidentities. -/
@[ext]
class PostLieAlgebra extends PostLieRing L, LieAlgebra R L, SMulCommClass R L L,
  IsScalarTower R L L

namespace PostLieRing

variable {R L : Type*} [CommRing R] [PostLieRing L]

@[simp]
lemma mul_bracket (x y z : L) : x * ⁅y, z⁆ = ⁅x * y, z⁆ + ⁅y, x * z⁆ :=
  PostLieRing.mul_bracket' x y z

@[simp]
lemma bracket_mul (x y z : L) : ⁅x, y⁆ * z = associator x y z - associator y x z :=
  PostLieRing.bracket_mul' x y z

/-- Every post-Lie algebra with vanishing bracket is a left pre-Lie algebra. -/
def instLeftPreLieRing (h : ∀ x y : L, ⁅x, y⁆ = 0) : LeftPreLieRing L where
  assoc_symm' x y z := by
    rw [← sub_eq_zero, ← zero_mul z, ← h x y]
    symm
    exact bracket_mul x y z

end PostLieRing

#lint
#min_imports
