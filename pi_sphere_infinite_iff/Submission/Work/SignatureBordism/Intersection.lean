import Mathlib
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.CapH
import Submission.Work.Cohomology.kronH_capPair_cup

/-!
# The intersection form of a closed oriented manifold

Let `X` be a simplicial set (in practice `X = toSSet.obj M` for a closed oriented smooth manifold
`M`) and let `c ∈ Hₙ(X;R)` be a homology class (in practice the fundamental class `[M]`, of degree
`n = dim M`).  The **intersection pairing** in complementary degrees `m`, `n - m` is

`(y, z) ↦ ⟨y ⌣ z, c⟩`,

the Kronecker pairing of the cup product with the fundamental class:

```lean
def interForm (m n : ℕ) (c : H_{m+n}(X;R)) : H^m(X;R) →ₗ[R] (H^n(X;R) →ₗ[R] R)
```

and the **middle intersection form** of a `2k`-dimensional manifold is the case `m = n = k`, whose
*quadratic form* `y ↦ ⟨y ⌣ y, c⟩` is

```lean
def interQuad (k : ℕ) (c : H_{2k}(X;R)) : QuadraticForm R (H^k(X;R))
```

The signature of `X` (see `Submission/Work/SignatureBordism/Sigma.lean`) is the signature of
`interQuad`, rationalised.

## Conventions and warnings

* The conventions are those of the cohomology chapter of this workspace: `cupH'` is the
  Alexander–Whitney cup product on `H^*(X;R)` (`Work.Cohomology.CupRing`), `kronH` the Kronecker
  pairing `H^n(X;R) →ₗ (H_n(X;R) →ₗ R)` (`Work.Cohomology.KroneckerH`) and `capPair` the cap
  product (`Work.Cohomology.CapH`).  The cap/cup identity `Work.Cohomology.kronH_capPair_cup`
  reads `⟨β, c ⌢ α⟩ = ⟨α ⌣ β, c⟩`, so that the intersection form is also
  `(y,z) ↦ ⟨z, c ⌢ y⟩` — see `interForm_apply_eq_kronH_capPair`.
* **No commutativity of the cup product is required.**  The quadratic form `interQuad` is built
  from the *raw* pairing `⟨y ⌣ z, c⟩`; its companion satisfies
  `Q(y + z) = Q y + Q z + (⟨y ⌣ z, c⟩ + ⟨z ⌣ y, c⟩)`, so the polarization of `Q` is the
  symmetrisation of the pairing.  This is why the signature chapter needs no Eilenberg–Zilber
  symmetry theorem.
* The pairing is *not* required to be symmetric: `interForm` is a bilinear form in its two
  cohomological variables.  In the middle degree of a `4k`-manifold it is symmetric because the
  cup product is graded commutative and the sign is `(-1)^{(2k)²} = +1`; that symmetry is not
  needed for the signature and is not proved here.
* The intersection form *depends on the choice of fundamental class*: replacing `c` by `-c`
  negates the form (`interForm_neg_fundamental`), which is precisely the statement that reversing
  the orientation of `M` negates its intersection form.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology

namespace Work.SignatureBordism

open Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-- **The intersection pairing of a closed oriented manifold**, in complementary degrees `m` and
`n`: the cup product followed by the Kronecker pairing against a homology class `c` (in practice
the fundamental class).

`interForm R X m n c y z = ⟨y ⌣ z, c⟩`. -/
noncomputable def interForm (m n : ℕ) (c : (chainC R X).homology (m + n)) :
    (cochainC R X).homology m →ₗ[R] ((cochainC R X).homology n →ₗ[R] R) :=
  LinearMap.mk₂ R
    (fun y z => kronH R X (m + n) (cupH' R X m n y z) c)
    (fun y₁ y₂ z => by simp only [map_add, LinearMap.add_apply])
    (fun a y z => by simp only [map_smul, LinearMap.smul_apply])
    (fun y z₁ z₂ => by simp only [map_add, LinearMap.add_apply])
    (fun a y z => by simp only [map_smul, LinearMap.smul_apply])

/-- **The computation rule** for `interForm`: it is the cup product evaluated against the class `c`.
This is the definitional unfolding of `interForm`; it is recorded as a `simp` lemma. -/
@[simp] theorem interForm_apply (m n : ℕ) (c : (chainC R X).homology (m + n))
    (y : (cochainC R X).homology m) (z : (cochainC R X).homology n) :
    interForm R X m n c y z = kronH R X (m + n) (cupH' R X m n y z) c :=
  rfl

/-- **The intersection form against the cap product.**  The defining identity of the intersection
pairing can be written with the cap product on the other side:

`⟨y ⌣ z, c⟩ = ⟨z, c ⌢ y⟩`.

This is the homology-level cap/cup identity `Work.Cohomology.kronH_capPair_cup`. -/
theorem interForm_apply_eq_kronH_capPair (m n : ℕ) (c : (chainC R X).homology (m + n))
    (y : (cochainC R X).homology m) (z : (cochainC R X).homology n) :
    interForm R X m n c y z = kronH R X n z (capPair R X m n y c) :=
  (kronH_capPair_cup R X m n y z c).symm

/-- The intersection form vanishes on the zero cohomology class. -/
@[simp] theorem interForm_zero_left (m n : ℕ) (c : (chainC R X).homology (m + n))
    (z : (cochainC R X).homology n) :
    interForm R X m n c 0 z = 0 := by
  simp only [map_zero, LinearMap.zero_apply]

/-- The intersection form vanishes on the zero cohomology class. -/
@[simp] theorem interForm_zero_right (m n : ℕ) (c : (chainC R X).homology (m + n))
    (y : (cochainC R X).homology m) :
    interForm R X m n c y 0 = 0 := by
  simp only [map_zero, LinearMap.zero_apply]

/-- Additivity of the intersection form in the first variable. -/
theorem interForm_add_left (m n : ℕ) (c : (chainC R X).homology (m + n))
    (y₁ y₂ : (cochainC R X).homology m) (z : (cochainC R X).homology n) :
    interForm R X m n c (y₁ + y₂) z = interForm R X m n c y₁ z + interForm R X m n c y₂ z := by
  simp only [map_add, LinearMap.add_apply]

/-- Additivity of the intersection form in the second variable. -/
theorem interForm_add_right (m n : ℕ) (c : (chainC R X).homology (m + n))
    (y : (cochainC R X).homology m) (z₁ z₂ : (cochainC R X).homology n) :
    interForm R X m n c y (z₁ + z₂) = interForm R X m n c y z₁ + interForm R X m n c y z₂ :=
  map_add ((interForm R X m n c) y) z₁ z₂

/-- The intersection form is linear in its first cohomological variable. -/
theorem interForm_smul_left (m n : ℕ) (a : R) (c : (chainC R X).homology (m + n))
    (y : (cochainC R X).homology m) (z : (cochainC R X).homology n) :
    interForm R X m n c (a • y) z = a • interForm R X m n c y z := by
  simp only [map_smul, LinearMap.smul_apply]

/-- The intersection form is linear in its second cohomological variable. -/
theorem interForm_smul_right (m n : ℕ) (a : R) (c : (chainC R X).homology (m + n))
    (y : (cochainC R X).homology m) (z : (cochainC R X).homology n) :
    interForm R X m n c y (a • z) = a • interForm R X m n c y z := by
  simp only [map_smul]

/-- **The intersection form scales in the fundamental class**: replacing `c` by `a • c` replaces
the form by `a` times itself.  (The case `a = -1` is `interForm_neg_fundamental`.) -/
theorem interForm_smul_fundamental (m n : ℕ) (a : R) (c : (chainC R X).homology (m + n))
    (y : (cochainC R X).homology m) (z : (cochainC R X).homology n) :
    interForm R X m n (a • c) y z = a • interForm R X m n c y z := by
  simp only [interForm_apply, map_smul]

/-- **Reversing the fundamental class negates the intersection form.**  (Reversing the orientation
of a closed oriented manifold negates its intersection form, hence also its signature.) -/
theorem interForm_neg_fundamental (m n : ℕ) (c : (chainC R X).homology (m + n))
    (y : (cochainC R X).homology m) (z : (cochainC R X).homology n) :
    interForm R X m n (-c) y z = -interForm R X m n c y z := by
  simpa using interForm_smul_fundamental R X m n (-1) c y z

/-- **The middle intersection form** of a closed oriented `2k`-manifold: the quadratic form
`y ↦ ⟨y ⌣ y, c⟩` on `H^k(X;R)`, where `c` is the fundamental class.

Its associated bilinear form (the companion of the quadratic map) is the symmetrisation
`(y,z) ↦ ⟨y ⌣ z, c⟩ + ⟨z ⌣ y, c⟩` of the intersection pairing; over a field of characteristic
`≠ 2` this determines the pairing. -/
noncomputable def interQuad (k : ℕ) (c : (chainC R X).homology (k + k)) :
    QuadraticForm R ((cochainC R X).homology k) :=
  QuadraticMap.mk (fun y => interForm R X k k c y y)
    (fun a y => by
      simp only [interForm_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring)
    ⟨LinearMap.mk₂ R (fun y z => interForm R X k k c y z + interForm R X k k c z y)
        (fun y₁ y₂ z => by
          simp only [interForm_add_left, interForm_add_right]; abel)
        (fun a y z => by
          simp only [interForm_smul_left, interForm_smul_right]; rw [smul_add])
        (fun y z₁ z₂ => by
          simp only [interForm_add_right, interForm_add_left]; abel)
        (fun a y z => by
          simp only [interForm_smul_right, interForm_smul_left]; rw [smul_add]),
      fun y z => by
        simp only [LinearMap.mk₂_apply, interForm_apply, map_add, LinearMap.add_apply]
        abel⟩

/-- **The computation rule for the middle intersection form**: on a class `y` it is
`⟨y ⌣ y, c⟩`. -/
@[simp] theorem interQuad_apply (k : ℕ) (c : (chainC R X).homology (k + k))
    (y : (cochainC R X).homology k) :
    interQuad R X k c y = interForm R X k k c y y :=
  rfl

/-- **Reversing the fundamental class negates the middle intersection form.** -/
theorem interQuad_neg_fundamental (k : ℕ) (c : (chainC R X).homology (k + k)) :
    interQuad R X k (-c) = -interQuad R X k c := by
  ext y
  simp only [interQuad_apply, interForm_neg_fundamental, neg_apply]

end

end Work.SignatureBordism
