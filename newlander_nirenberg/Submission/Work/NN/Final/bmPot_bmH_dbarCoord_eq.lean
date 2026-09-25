import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Final.bmPot_dbarCoord_three

namespace Work.NN.Final

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open Work.CR.Flat Work.NN.Core

noncomputable section

variable {n : ℕ}

/-! ### Elementary `∂̄`-calculus and support lemmas

The private lemmas of `Submission/Work/NN/Core/bmDefectClosed.lean`, restated for a cutoff of
class `C²` (rather than `C^∞`) and with the `C¹`-consequences we need here. -/

/-- `∂̄_m χ` is differentiable wherever `χ` is twice (real) differentiable. -/
private lemma dbarDiff {χ : Cn n → ℂ} {w : Cn n} (m : Fin n) (hχ : ContDiffAt ℝ 2 χ w) :
    DifferentiableAt ℝ (dbarCoord m χ) w := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ χ) w := hχ.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 1 (dbarCoord m χ) w := by
    rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
    exact (Work.CR.Flat.Polydisc.dbarCoordPhi m).contDiff.contDiffAt.comp w h1
  exact h2.differentiableAt (by norm_num)

/-- `∂̄_x` of `w ↦ ∂̄_m χ w · ζ w`, with the two `∂̄`-derivatives commuted. -/
private lemma dbarDbarMul {χ ζ : Cn n → ℂ} {m x : Fin n} {w : Cn n}
    (hχ : ContDiffAt ℝ 2 χ w) (hζ : DifferentiableAt ℝ ζ w) :
    dbarCoord x (fun y => dbarCoord m χ y * ζ y) w
      = dbarCoord m (dbarCoord x χ) w * ζ w + dbarCoord m χ w * dbarCoord x ζ w := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul x (dbarCoord m χ) ζ w
      (dbarDiff m hχ) hζ,
    Work.CR.Flat.Polydisc.dbarCoord_comm x m χ w hχ]

/-- Additivity of `∂̄_j` for functions written as `w ↦ u w - v w`. -/
private lemma dbarSub (j : Fin n) (u v : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord j (fun w => u w - v w) z = dbarCoord j u z - dbarCoord j v z := by
  have hfd : fderiv ℝ (fun w => u w - v w) z = fderiv ℝ u z - fderiv ℝ v z := by
    rw [show (fun w => u w - v w) = u - v from rfl, fderiv_sub hu hv]
  simp only [dbarCoord, hfd, sub_apply]
  ring

/-- `∂̄_k χ` is `C¹` when `χ` is `C²`. -/
private lemma contDiff_one_dbarCoord {χ : Cn n → ℂ} (hχ : ContDiff ℝ 2 χ) (m : Fin n) :
    ContDiff ℝ 1 (dbarCoord m χ) := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi m).contDiff.comp (hχ.fderiv_right (by norm_num))

/-- The components of `bmH χ η` are `C¹` when `χ` is `C²` and `η` is `C¹`. -/
private lemma contDiff_one_bmH {χ : Cn n → ℂ} (hχ : ContDiff ℝ 2 χ)
    {η : Fin n → Fin n → Cn n → ℂ} (hη : ∀ i l, ContDiff ℝ 1 (η i l)) (a b c : Fin n) :
    ContDiff ℝ 1 (bmH χ η a b c) := by
  unfold bmH
  exact ((((contDiff_one_dbarCoord hχ c).mul (hη a b)).add
    ((contDiff_one_dbarCoord hχ a).mul (hη b c))).sub
      ((contDiff_one_dbarCoord hχ b).mul (hη a c)))

/-- A compactly supported function vanishes outside a closed ball of positive radius. -/
private lemma exists_radius_of_hasCompactSupport {g : Cn n → ℂ} (hcs : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, R ≤ ‖x‖ → g x = 0 := by
  have hb : Bornology.IsBounded (tsupport g) := IsCompact.isBounded hcs
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  refine ⟨max C 0 + 1, by positivity, fun x hx => ?_⟩
  by_contra hne
  have hxmem : x ∈ tsupport g := subset_tsupport g (Function.mem_support.mpr hne)
  have h1 := hC x hxmem
  have h2 : max C 0 + 1 ≤ ‖x‖ := hx
  have h3 : C ≤ max C 0 := le_max_left C 0
  linarith

/-- The components of `bmH χ η` have compact support when `χ` does:
`bmH χ η a b c = ∂̄_c χ · η_{ab} + ∂̄_a χ · η_{bc} - ∂̄_b χ · η_{ac}` vanishes off the support
of `χ`. -/
private lemma hasCompactSupport_bmH {χ : Cn n → ℂ} (hcs : HasCompactSupport χ)
    (η : Fin n → Fin n → Cn n → ℂ) (a b c : Fin n) :
    HasCompactSupport (bmH χ η a b c) := by
  obtain ⟨R, _hR, hsupp⟩ := exists_radius_of_hasCompactSupport hcs
  refine Work.CR.Flat.Cauchy.bmPotDbar_hasCompactSupport_of_norm (R := R + 1) fun x hx => ?_
  have hx' : R < ‖x‖ := by linarith
  unfold bmH
  rw [Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_lt_norm hsupp c hx',
      Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_lt_norm hsupp a hx',
      Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_lt_norm hsupp b hx']
  ring

/-- A function vanishing off its (closed) topological support has vanishing `∂̄` at every point
outside that support. -/
private lemma dbarCoord_eq_zero_of_notMem_tsupport {g : Cn n → ℂ} {w : Cn n}
    (hw : w ∉ tsupport g) (k : Fin n) : dbarCoord k g w = 0 := by
  have hn : (tsupport g)ᶜ ∈ 𝓝 w := (isClosed_tsupport g).isOpen_compl.mem_nhds hw
  have heq : g =ᶠ[𝓝 w] (fun _ : Cn n => 0) := by
    filter_upwards [hn] with y hy
    have hy' : y ∉ Function.support g := fun hgy => hy (subset_tsupport g hgy)
    simpa only [Function.mem_support, ne_eq, not_not] using hy'
  have hfd : fderiv ℝ g w = 0 := by
    rw [heq.fderiv_eq, fderiv_const_apply]
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  simp [Function.comp_apply, hfd]

/-! ### The `(0,4)`-algebra identity for `bmH` -/

/-- **Pointwise algebra identity for the four-index `∂̄`-combination of `bmH`.**

With `bmH χ η a b c = ∂̄_c χ · η_{ab} + ∂̄_a χ · η_{bc} - ∂̄_b χ · η_{ac}`, the alternating
four-index combination of the `∂̄` of `bmH χ η` equals the `∂̄χ`-contraction of the four
`(0,2)`-closedness expressions of `η`:

`∂̄_j (bmH_{lmi}) - ∂̄_l (bmH_{jmi}) + ∂̄_m (bmH_{jli}) - ∂̄_i (bmH_{jlm})`

`= ∂̄_i χ · (∂̄_j η_{lm} - ∂̄_l η_{jm} + ∂̄_m η_{jl})`

`+ ∂̄_l χ · (∂̄_j η_{mi} - ∂̄_m η_{ji} + ∂̄_i η_{jm})`

`- ∂̄_m χ · (∂̄_j η_{li} - ∂̄_l η_{ji} + ∂̄_i η_{jl})`

`- ∂̄_j χ · (∂̄_l η_{mi} - ∂̄_m η_{li} + ∂̄_i η_{lm})`.

This is the `(0,4)`-form statement `∂̄(∂̄χ ∧ η) = ∂̄²χ ∧ η - ∂̄χ ∧ ∂̄η`: the second-derivative
part `∂̄²χ ∧ η` cancels by commutation of the `∂̄`-derivatives of the `C²` function `χ`, and the
first-derivative part is `-∂̄χ ∧ ∂̄η`, i.e. minus the `∂̄χ`-contraction of the failure of `η` to
be `∂̄`-closed.  The identity itself needs no closedness hypothesis. -/
private theorem bmH_dbar_four {χ : Cn n → ℂ} (hχ : ContDiff ℝ 2 χ)
    {η : Fin n → Fin n → Cn n → ℂ} (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (j l m i : Fin n) (w : Cn n) :
    dbarCoord j (bmH χ η l m i) w - dbarCoord l (bmH χ η j m i) w
      + dbarCoord m (bmH χ η j l i) w - dbarCoord i (bmH χ η j l m) w
    = dbarCoord i χ w * (dbarCoord j (η l m) w - dbarCoord l (η j m) w + dbarCoord m (η j l) w)
      + dbarCoord l χ w * (dbarCoord j (η m i) w - dbarCoord m (η j i) w + dbarCoord i (η j m) w)
      - dbarCoord m χ w * (dbarCoord j (η l i) w - dbarCoord l (η j i) w + dbarCoord i (η j l) w)
      - dbarCoord j χ w * (dbarCoord l (η m i) w - dbarCoord m (η l i) w + dbarCoord i (η l m) w) := by
  have hχ2 : ContDiffAt ℝ 2 χ w := hχ.contDiffAt
  have hd : ∀ p : Fin n, DifferentiableAt ℝ (dbarCoord p χ) w := fun p => dbarDiff p hχ2
  have hηd : ∀ p q : Fin n, DifferentiableAt ℝ (η p q) w :=
    fun p q => ((hη p q).differentiable one_ne_zero).differentiableAt
  have hcl : ∀ p q : Fin n, dbarCoord q (dbarCoord p χ) w = dbarCoord p (dbarCoord q χ) w :=
    fun p q => Work.CR.Flat.Polydisc.dbarCoord_comm p q χ w hχ2
  have h1 : dbarCoord j (bmH χ η l m i) w
      = dbarCoord i (dbarCoord j χ) w * η l m w + dbarCoord i χ w * dbarCoord j (η l m) w
        + dbarCoord l (dbarCoord j χ) w * η m i w + dbarCoord l χ w * dbarCoord j (η m i) w
        - dbarCoord m (dbarCoord j χ) w * η l i w - dbarCoord m χ w * dbarCoord j (η l i) w := by
    unfold bmH
    rw [dbarSub j (fun y => dbarCoord i χ y * η l m y + dbarCoord l χ y * η m i y)
          (fun y => dbarCoord m χ y * η l i y) w
          (((hd i).mul (hηd l m)).add ((hd l).mul (hηd m i))) ((hd m).mul (hηd l i)),
        Work.CR.Flat.Polydisc.dbarCoord_add j (fun y => dbarCoord i χ y * η l m y)
          (fun y => dbarCoord l χ y * η m i y) w
          ((hd i).mul (hηd l m)) ((hd l).mul (hηd m i)),
        dbarDbarMul hχ2 (hηd l m), dbarDbarMul hχ2 (hηd m i), dbarDbarMul hχ2 (hηd l i)]
    ring
  have h2 : dbarCoord l (bmH χ η j m i) w
      = dbarCoord i (dbarCoord l χ) w * η j m w + dbarCoord i χ w * dbarCoord l (η j m) w
        + dbarCoord j (dbarCoord l χ) w * η m i w + dbarCoord j χ w * dbarCoord l (η m i) w
        - dbarCoord m (dbarCoord l χ) w * η j i w - dbarCoord m χ w * dbarCoord l (η j i) w := by
    unfold bmH
    rw [dbarSub l (fun y => dbarCoord i χ y * η j m y + dbarCoord j χ y * η m i y)
          (fun y => dbarCoord m χ y * η j i y) w
          (((hd i).mul (hηd j m)).add ((hd j).mul (hηd m i))) ((hd m).mul (hηd j i)),
        Work.CR.Flat.Polydisc.dbarCoord_add l (fun y => dbarCoord i χ y * η j m y)
          (fun y => dbarCoord j χ y * η m i y) w
          ((hd i).mul (hηd j m)) ((hd j).mul (hηd m i)),
        dbarDbarMul hχ2 (hηd j m), dbarDbarMul hχ2 (hηd m i), dbarDbarMul hχ2 (hηd j i)]
    ring
  have h3 : dbarCoord m (bmH χ η j l i) w
      = dbarCoord i (dbarCoord m χ) w * η j l w + dbarCoord i χ w * dbarCoord m (η j l) w
        + dbarCoord j (dbarCoord m χ) w * η l i w + dbarCoord j χ w * dbarCoord m (η l i) w
        - dbarCoord l (dbarCoord m χ) w * η j i w - dbarCoord l χ w * dbarCoord m (η j i) w := by
    unfold bmH
    rw [dbarSub m (fun y => dbarCoord i χ y * η j l y + dbarCoord j χ y * η l i y)
          (fun y => dbarCoord l χ y * η j i y) w
          (((hd i).mul (hηd j l)).add ((hd j).mul (hηd l i))) ((hd l).mul (hηd j i)),
        Work.CR.Flat.Polydisc.dbarCoord_add m (fun y => dbarCoord i χ y * η j l y)
          (fun y => dbarCoord j χ y * η l i y) w
          ((hd i).mul (hηd j l)) ((hd j).mul (hηd l i)),
        dbarDbarMul hχ2 (hηd j l), dbarDbarMul hχ2 (hηd l i), dbarDbarMul hχ2 (hηd j i)]
    ring
  have h4 : dbarCoord i (bmH χ η j l m) w
      = dbarCoord m (dbarCoord i χ) w * η j l w + dbarCoord m χ w * dbarCoord i (η j l) w
        + dbarCoord j (dbarCoord i χ) w * η l m w + dbarCoord j χ w * dbarCoord i (η l m) w
        - dbarCoord l (dbarCoord i χ) w * η j m w - dbarCoord l χ w * dbarCoord i (η j m) w := by
    unfold bmH
    rw [dbarSub i (fun y => dbarCoord m χ y * η j l y + dbarCoord j χ y * η l m y)
          (fun y => dbarCoord l χ y * η j m y) w
          (((hd m).mul (hηd j l)).add ((hd j).mul (hηd l m))) ((hd l).mul (hηd j m)),
        Work.CR.Flat.Polydisc.dbarCoord_add i (fun y => dbarCoord m χ y * η j l y)
          (fun y => dbarCoord j χ y * η l m y) w
          ((hd m).mul (hηd j l)) ((hd j).mul (hηd l m)),
        dbarDbarMul hχ2 (hηd j l), dbarDbarMul hχ2 (hηd l m), dbarDbarMul hχ2 (hηd j m)]
    ring
  rw [h1, h2, h3, h4, hcl i j, hcl j l, hcl j m, hcl l i, hcl l m, hcl m i]
  ring

/-- The four-index combination of `∂̄ (bmH χ η)` vanishes: the `∂̄²χ ∧ η` part cancels by
commutation of the `∂̄`-derivatives of `χ ∈ C²`, and the `∂̄χ ∧ ∂̄η` part vanishes because every
term carries a factor `∂̄_k χ`, which is zero off the support of `χ`, where `η` is `∂̄`-closed. -/
private lemma bmH_dbar_four_zero {χ : Cn n → ℂ} (hχ : ContDiff ℝ 2 χ)
    {U : Set (Cn n)} (htU : tsupport χ ⊆ U)
    {η : Fin n → Fin n → Cn n → ℂ} (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hclosed : ∀ j k m (z : Cn n), z ∈ U →
      dbarCoord j (η k m) z - dbarCoord k (η j m) z + dbarCoord m (η j k) z = 0)
    (j l m i : Fin n) (w : Cn n) :
    dbarCoord j (bmH χ η l m i) w - dbarCoord l (bmH χ η j m i) w
      + dbarCoord m (bmH χ η j l i) w - dbarCoord i (bmH χ η j l m) w = 0 := by
  rw [bmH_dbar_four hχ hη j l m i w]
  by_cases hw : w ∈ U
  · rw [hclosed j l m w hw, hclosed j m i w hw, hclosed j l i w hw, hclosed l m i w hw]
    ring
  · have hwt : w ∉ tsupport χ := fun h => hw (htU h)
    have h0 : ∀ k : Fin n, dbarCoord k χ w = 0 :=
      fun k => dbarCoord_eq_zero_of_notMem_tsupport hwt k
    rw [h0 i, h0 l, h0 m, h0 j]
    ring

/-- **The `∂̄` of the Bochner–Martinelli potential of `∂̄χ ∧ η` is that `(0,3)`-form itself**
(at the level of the `(0,2)`-form combination), for `η` closed on a neighbourhood of
`tsupport χ`.

Let `χ` be a `C²` cut-off with compact support, `U` an open set with `tsupport χ ⊆ U`, `η` a `C¹`
family which is `∂̄`-closed on `U`, and put

`Y j l m i w := bmH χ η j l m w = ∂̄_m χ w * η j l w + ∂̄_j χ w * η l m w - ∂̄_l χ w * η j m w`

(the `(0,3)`-form `∂̄χ ∧ η`; it involves *no* derivative of `η`).  Then

`∂̄_j (bmPot (Y l m ·)) - ∂̄_l (bmPot (Y j m ·)) + ∂̄_m (bmPot (Y j l ·)) = bmGamma n * Y j l m z`.

This is the `(0,3)`-level Bochner–Martinelli identity `Work.NN.Final.bmPot_dbarCoord_three`
applied to `Y`, in which the additional integral term

`∑ i, ∫ x, bmKernel i x * (∂̄_j Y l m i - ∂̄_l Y j m i + ∂̄_m Y j l i - ∂̄_i Y j l m) (z + x)`

vanishes identically because it is the `(0,4)`-form `∂̄(∂̄χ ∧ η) = ∂̄²χ ∧ η - ∂̄χ ∧ ∂̄η`: the
`χ`-second-derivative part cancels pairwise by `dbarCoord_comm` (`χ ∈ C²`), and the part
`(∂̄χ)·(∂̄η)` vanishes because the support of `∂̄χ` is contained in `tsupport χ ⊆ U`, where `η` is
closed.  Note that no hypothesis of the form `χ z = 1` is imposed: the identity holds pointwise
everywhere, and the vanishing of the right-hand side at the points where `χ ≡ 1` near `z` is
derived in the file that uses this lemma. -/
theorem bmPot_bmH_dbarCoord_eq {n : ℕ} (hn : 0 < n) {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ 2 χ)
    (hcs : HasCompactSupport χ) {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (htU : tsupport χ ⊆ U)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hclosed : ∀ j k m (z : Fin n → ℂ), z ∈ U →
      Work.CR.Flat.dbarCoord j (η k m) z - Work.CR.Flat.dbarCoord k (η j m) z
        + Work.CR.Flat.dbarCoord m (η j k) z = 0) :
    ∀ (j l m : Fin n) (z : Fin n → ℂ),
      Work.CR.Flat.dbarCoord j
          (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η l m i) w) z
        - Work.CR.Flat.dbarCoord l
          (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j m i) w) z
        + Work.CR.Flat.dbarCoord m
          (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) w) z
      = Work.CR.Flat.Cauchy.bmGamma n * Work.NN.Core.bmH χ η j l m z := by
  have _ := hU
  intro j l m z
  -- the extra integral term of the `(0,3)`-level identity vanishes identically
  have hzero : (∑ i : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel i x *
      (Work.CR.Flat.dbarCoord j (Work.NN.Core.bmH χ η l m i) (z + x)
        - Work.CR.Flat.dbarCoord l (Work.NN.Core.bmH χ η j m i) (z + x)
        + Work.CR.Flat.dbarCoord m (Work.NN.Core.bmH χ η j l i) (z + x)
        - Work.CR.Flat.dbarCoord i (Work.NN.Core.bmH χ η j l m) (z + x))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hfun : (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel i x *
        (Work.CR.Flat.dbarCoord j (Work.NN.Core.bmH χ η l m i) (z + x)
          - Work.CR.Flat.dbarCoord l (Work.NN.Core.bmH χ η j m i) (z + x)
          + Work.CR.Flat.dbarCoord m (Work.NN.Core.bmH χ η j l i) (z + x)
          - Work.CR.Flat.dbarCoord i (Work.NN.Core.bmH χ η j l m) (z + x))) = fun _ => (0 : ℂ) := by
      funext x
      rw [bmH_dbar_four_zero hχ htU hη hclosed j l m i (z + x), mul_zero]
    rw [hfun, integral_zero]
  have hthree := bmPot_dbarCoord_three (n := n) hn (Y := fun a b c => Work.NN.Core.bmH χ η a b c)
    (fun a b c => contDiff_one_bmH hχ hη a b c)
    (fun a b c => hasCompactSupport_bmH hcs η a b c) j l m z
  rw [hzero, add_zero] at hthree
  exact hthree

end

end Work.NN.Final
