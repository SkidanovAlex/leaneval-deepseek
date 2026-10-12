import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseFixB2.Polar.neuFrac_parallelogram
import Submission.Work.BoseFixB2.Polar.polB_bilinear
import Submission.Work.BoseFixB2.Polar.polarForm_add
import Submission.Work.BoseKinLoc.Word.fsT_const_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.KinOffdiag.fsTbil_add_left` — additivity of `fsTbil` in its first state

`Work.BoseFixB2.fsTbil ℓ d s εT b u f g` is the polarisation of FS §6's one-body localised
kinetic word `fsT` (`eq:DefT`),

`fsTbil u f g = (fsT u (f+g) − fsT u (f−g)) / 4`,

i.e. the bilinear form whose diagonal is `fsT u`.  The off-diagonal slot integrals of the
localised box word are exactly the `indU`-weighted box integrals of `fsTbil` of two slot
fibres (`Polar.slot_polar`), so the additivity of `fsTbil` in each state is what makes those
slot integrals genuinely bilinear; this file proves additivity in the **first** state.

## The argument

Polarisation is additive as soon as the diagonal is a quadratic form: for *any* `Q` and
*any* predicate `G` closed under `+` and `−` satisfying the parallelogram law on `G`,
the four instances

`Q(u+v+y) + Q(u−v+y) = 2Q(u+y) + 2Qv`,   `Q(u+v−y) + Q(u−v−y) = 2Q(u−y) + 2Qv`,
`Q(u+v+y) + Q(u−v−y) = 2Qu + 2Q(v+y)`,   `Q(u+v−y) + Q(u−v+y) = 2Qu + 2Q(v−y)`

combine linearly to `Q(u+v+y) − Q(u+v−y) = [Q(u+y) − Q(u−y)] + [Q(v+y) − Q(v−y)]`
(`par_polar_add_left`).  Neither homogeneity nor evenness of `Q` is needed.

It therefore remains to establish the parallelogram law for `fsT u` under the *weak*
hypotheses of the requested statement — only `ℓ > 0` on the parameters, the signs of
`d, s, ε_T, b` being unrestricted.  Indeed `fsT = neuWord + gapWord + momWord + mainWord` and
each summand is the diagonal of a bilinear form:

* `gapWord = bℓ⁻²·gapBare` (`FsTAux.gapBare_parallelogram`, needing only `ℓ > 0`),
* `momWord = bε_T(dℓ)⁻²·momForm` (`FsTAux.momForm_parallelogram_aux`, only `ℓ > 0`),
* `mainWord = (1−ε_T)·bsOneBody(ℓ,(2sℓ)⁻¹) + ε_T·bsOneBody(ℓ,(2dsℓ)⁻¹)`
  (`FsTAux.bsOneBody_parallelogram_aux`, only `ℓ > 0`),
* `neuWord ℓ d ε_T u ψ = ½ε_T(dℓ)⁻²·neuFrac ℓ ((dℓ)⁻²) u (Q_uψ)`.  Here `neuFrac` is the `sInf`
  of the Dirichlet trial functional; its parallelogram identity
  (`FsTAux.neuFrac_parallelogram_aux`) is available for `a² = (dℓ)⁻² > 0`, i.e. for `d ≠ 0`,
  `Q_u` being linear in `ψ` (`FsTAux.Qfree_add`, `FsTAux.Qfree_sub`).  If `d = 0` then
  `(dℓ)⁻² = 0` by `zero_zpow`, so `neuWord ≡ 0` and the identity is trivial.

This is the only place where a degenerate parameter matters; `Polar.fsT_parallelogram` records
the strictly positive case `d, s, ε_T, b > 0`, which is the one used by the §6 band arguments.

The two facts are combined in `fsTbil_add_left`.
-/

namespace Work.BoseFixB2.DvApriori.KinOffdiag

open Work.BoseKinLoc Work.BSKinetic

/-! ## 1. The abstract layer: the polarisation of a parallelogram-law function -/

/-- **Additivity of the polar form in the first slot**, from the parallelogram law on a set `G`
of admissible states closed under `+` and `−`.

For `Q : V → ℝ` and `G : V → Prop` with
`Q (x+y) + Q (x−y) = 2Q x + 2Q y` whenever `x, y ∈ G`, the polar form
`B x y = (Q (x+y) − Q (x−y)) / 4` is additive in its first variable.

The proof is the classical linear combination of the four instances of the parallelogram law
at the pairs `(u+y, v)`, `(u−y, v)`, `(u, v+y)`, `(u, v−y)`; neither homogeneity nor evenness
of `Q` is needed. -/
theorem par_polar_add_left {V : Type*} [AddCommGroup V] (Q : V → ℝ) (G : V → Prop)
    (hpar : ∀ x y : V, G x → G y → Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hadd : ∀ x y : V, G x → G y → G (x + y))
    (hsub : ∀ x y : V, G x → G y → G (x - y))
    {u v y : V} (hu : G u) (hv : G v) (hy : G y) :
    (Q ((u + v) + y) - Q ((u + v) - y)) / 4
      = (Q (u + y) - Q (u - y)) / 4 + (Q (v + y) - Q (v - y)) / 4 := by
  have h1 := hpar (u + y) v (hadd u y hu hy) hv
  have h2 := hpar (u - y) v (hsub u y hu hy) hv
  have h3 := hpar u (v + y) hu (hadd v y hv hy)
  have h4 := hpar u (v - y) hu (hsub v y hv hy)
  rw [show (u + y) + v = u + v + y by abel, show (u + y) - v = u - v + y by abel] at h1
  rw [show (u - y) + v = u + v - y by abel, show (u - y) - v = u - v - y by abel] at h2
  rw [show u + (v + y) = u + v + y by abel, show u - (v + y) = u - v - y by abel] at h3
  rw [show u + (v - y) = u + v - y by abel, show u - (v - y) = u - v + y by abel] at h4
  linarith

/-! ## 2. The parallelogram law for `fsT` with unrestricted parameters (`ℓ > 0` only) -/

/-- **The parallelogram identity for FS's localised kinetic word `fsT` under the weak
parameter assumptions**: only `ℓ > 0` is required, the signs of `d, s, ε_T, b` are free.

`fsT = neuWord + gapWord + momWord + mainWord`; the last three summands are quadratic forms
in `ψ` by `FsTAux.gapBare_parallelogram`, `FsTAux.momForm_parallelogram_aux` and
`FsTAux.bsOneBody_parallelogram_aux` (all of which need only `ℓ > 0`), while
`neuWord ℓ d ε_T u ψ = ½ε_T(dℓ)⁻²·neuFrac ℓ ((dℓ)⁻²) u (Q_uψ)` is a quadratic form because
* for `d ≠ 0` the parameter `a² = (dℓ)⁻²` is positive and
  `FsTAux.neuFrac_parallelogram_aux` applies, `Q_u` being linear in `ψ`
  (`FsTAux.Qfree_add`, `FsTAux.Qfree_sub`);
* for `d = 0` the prefactor `(dℓ)⁻²` vanishes (`zero_zpow`), so `neuWord ≡ 0`. -/
theorem fsT_parallelogram_gen {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => f z + g z)
      + Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => f z - g z)
      = 2 * Work.BoseKinLoc.fsT ℓ d s εT b u f
        + 2 * Work.BoseKinLoc.fsT ℓ d s εT b u g := by
  have hQf : ContDiff ℝ (⊤ : ℕ∞) (Qfree ℓ u f) := by
    have h' : Qfree ℓ u f = fun z => f z - bsMean ℓ u f := rfl
    rw [h']; exact hf.sub contDiff_const
  have hQg : ContDiff ℝ (⊤ : ℕ∞) (Qfree ℓ u g) := by
    have h' : Qfree ℓ u g = fun z => g z - bsMean ℓ u g := rfl
    rw [h']; exact hg.sub contDiff_const
  have hneu : neuWord ℓ d εT u (fun z => f z + g z) + neuWord ℓ d εT u (fun z => f z - g z)
      = 2 * neuWord ℓ d εT u f + 2 * neuWord ℓ d εT u g := by
    unfold neuWord
    rw [Work.BoseFixB2.Polar.FsTAux.Qfree_add hℓ u hf.continuous hg.continuous,
      Work.BoseFixB2.Polar.FsTAux.Qfree_sub hℓ u hf.continuous hg.continuous]
    by_cases hd : d = 0
    · -- the degenerate case: the prefactor `(dℓ)⁻²` vanishes, so `neuWord ≡ 0`
      have hz : (d * ℓ) ^ (-2 : ℤ) = 0 := by rw [hd, zero_mul]; norm_num
      rw [hz]; ring
    · have ha2 : 0 < (d * ℓ) ^ (-2 : ℤ) := by
        have hne : d * ℓ ≠ 0 := mul_ne_zero hd (ne_of_gt hℓ)
        positivity
      have hpar := Work.BoseFixB2.Polar.FsTAux.neuFrac_parallelogram_aux (ℓ := ℓ)
        (a2 := (d * ℓ) ^ (-2 : ℤ)) hℓ ha2 u hQf hQg
      linear_combination ((1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ)) * hpar
  have hgap : gapWord ℓ b u (fun z => f z + g z) + gapWord ℓ b u (fun z => f z - g z)
      = 2 * gapWord ℓ b u f + 2 * gapWord ℓ b u g := by
    unfold gapWord
    have hpar :=
      Work.BoseFixB2.Polar.FsTAux.gapBare_parallelogram hℓ u hf.continuous hg.continuous
    linear_combination (b * ℓ ^ (-2 : ℤ)) * hpar
  have hmom : momWord ℓ d εT b u (fun z => f z + g z) + momWord ℓ d εT b u (fun z => f z - g z)
      = 2 * momWord ℓ d εT b u f + 2 * momWord ℓ d εT b u g := by
    unfold momWord
    have hpar := Work.BoseFixB2.Polar.FsTAux.momForm_parallelogram_aux (d := d) hℓ u hf hg
    linear_combination (b * εT * (d * ℓ) ^ (-2 : ℤ)) * hpar
  have hmain : mainWord ℓ d s εT u (fun z => f z + g z) + mainWord ℓ d s εT u (fun z => f z - g z)
      = 2 * mainWord ℓ d s εT u f + 2 * mainWord ℓ d s εT u g := by
    unfold mainWord
    have h1 := Work.BoseFixB2.Polar.FsTAux.bsOneBody_parallelogram_aux (c := (2 * (s * ℓ))⁻¹)
      hℓ u hf hg
    have h2 := Work.BoseFixB2.Polar.FsTAux.bsOneBody_parallelogram_aux (c := (2 * (d * s * ℓ))⁻¹)
      hℓ u hf hg
    linear_combination (1 - εT) * h1 + εT * h2
  rw [Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b u (fun z => f z + g z),
    Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b u (fun z => f z - g z),
    Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b u f,
    Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b u g]
  linear_combination hneu + hgap + hmom + hmain

/-! ## 3. Additivity of `fsTbil` in the first state -/

/-- **The polarised one-body word `fsTbil` is additive in its first state.**  With
`Q = fsT ℓ d s εT b 0`, the parallelogram law `fsT_parallelogram_gen` feeds the abstract
additivity `par_polar_add_left` at `u = f`, `v = g`, `y = h`. -/
theorem fsTbil_add_left {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {f g h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    Work.BoseFixB2.fsTbil ℓ d s εT b 0 (fun z => f z + g z) h
      = Work.BoseFixB2.fsTbil ℓ d s εT b 0 f h + Work.BoseFixB2.fsTbil ℓ d s εT b 0 g h := by
  have key := par_polar_add_left (Q := fun ψ => Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ)
    (G := fun ψ => ContDiff ℝ (⊤ : ℕ∞) ψ)
    (fun x y hx hy => fsT_parallelogram_gen hℓ 0 hx hy)
    (fun x y hx hy => hx.add hy) (fun x y hx hy => hx.sub hy) hf hg hh
  unfold Work.BoseFixB2.fsTbil
  exact key

end Work.BoseFixB2.DvApriori.KinOffdiag
