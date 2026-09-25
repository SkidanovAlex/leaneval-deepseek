import Mathlib
import Submission.Work.NN.Seeley.Setup

/-!
# Iterated derivatives of the Seeley sum on the open lower half space

On the open lower half space `{p.2 < 0}` the Seeley sum `seeleySumV a b δ g` is locally a finite
sum of the terms `seeleyTV a b δ g m`: for `p` with `p.2 < 0`, the terms with `b m ≥ 2/|p.2|`
already vanish on a whole neighbourhood of `p` (the cutoff `seeleyCut` is zero once its argument
exceeds `2` in absolute value).

Consequently the `k`-th iterated derivative of the sum at such a point is the (finite, hence
convergent) sum of the `k`-th iterated derivatives of the terms.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

namespace Work.NN.Seeley

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The `m`-th Seeley term is smooth of every order (it is a product of the smooth cutoff
composition, the smooth localised function composed with a linear map, and a constant). -/
lemma seeleyTV_contDiff {δ : ℝ} (hδ : 0 < δ) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2})
    (a b : ℕ → ℝ) (k : ℕ) (m : ℕ) :
    ContDiff ℝ (k : WithTop ENat) (Work.NN.Final.seeleyTV a b δ g m) := by
  have hu : ContDiff ℝ (k : WithTop ENat) (Work.NN.Final.seeleyV δ g) :=
    Work.NN.Final.seeleyV_contDiff_fin hδ hg k
  have hL : ContDiff ℝ (k : WithTop ENat) (fun p : X × ℝ => (p.1, -(b m) * p.2)) := by
    let L : X × ℝ →L[ℝ] X × ℝ :=
      (ContinuousLinearMap.fst ℝ X ℝ).prod ((-(b m)) • ContinuousLinearMap.snd ℝ X ℝ)
    have hL' : (fun p : X × ℝ => (p.1, -(b m) * p.2)) = ⇑L := by
      funext p; simp [L, ContinuousLinearMap.prod_apply]
    rw [hL']; exact ContinuousLinearMap.contDiff L
  have hcomp : ContDiff ℝ (k : WithTop ENat)
      (fun p : X × ℝ => Work.NN.Final.seeleyV δ g (p.1, -(b m) * p.2)) := hu.comp hL
  have hcut : ContDiff ℝ (k : WithTop ENat)
      (fun p : X × ℝ => Work.NN.Final.seeleyCut (-(b m) * p.2)) := by
    have h2 : ContDiff ℝ (k : WithTop ENat) (fun p : X × ℝ => -(b m) * p.2) := by
      have h2' : (fun p : X × ℝ => -(b m) * p.2)
          = ⇑(((-(b m)) : ℝ) • ContinuousLinearMap.snd ℝ X ℝ) := by
        funext p; simp
      rw [h2']; exact ContinuousLinearMap.contDiff _
    exact (Work.NN.Final.seeleyCut_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).comp h2
  exact ContDiff.const_smul (a m) (hcut.smul hcomp)

/-- The `m`-th Seeley term vanishes at a point `q` that is (strictly) closer to the hyperplane
than `p`, provided `b m` is large enough compared with `|p.2|`. -/
lemma seeleyTV_eq_zero_of_lt {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m) (δ : ℝ)
    (g : X × ℝ → ℂ) {p q : X × ℝ} {M m : ℕ}
    (hM : ∀ j ≥ M, 2 / (-(p.2 / 2)) ≤ b j) (hm : M ≤ m)
    (hp : p.2 < 0) (hq : q.2 < p.2 / 2) :
    Work.NN.Final.seeleyTV a b δ g m q = 0 := by
  have hqabs : 0 < -(p.2 / 2) := by linarith
  have hle : 2 / (-(p.2 / 2)) ≤ b m := hM m hm
  have hge : 2 ≤ b m * (-(p.2 / 2)) := by rw [div_le_iff₀ hqabs] at hle; linarith
  have hqneg : q.2 < 0 := by linarith
  have harg : 2 ≤ |-(b m) * q.2| := by
    rw [Work.NN.Final.abs_neg_mul, abs_of_nonneg (by linarith [hb m] : (0:ℝ) ≤ b m),
      abs_of_neg hqneg]
    nlinarith
  simp only [Work.NN.Final.seeleyTV, Work.NN.Final.seeleyCut_eq_zero harg, zero_smul, smul_zero]

/-- Near a point `p` of the open lower half space the Seeley sum is a finite sum of the terms, and
all the terms outside that finite set vanish identically on a neighbourhood of `p`. -/
lemma exists_finset_seeleySumV_eventuallyEq {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (δ : ℝ) (g : X × ℝ → ℂ)
    {p : X × ℝ} (hp : p.2 < 0) :
    ∃ S : Finset ℕ,
      (Work.NN.Final.seeleySumV a b δ g =ᶠ[𝓝 p]
          fun q => ∑ m ∈ S, Work.NN.Final.seeleyTV a b δ g m q) ∧
      (∀ m ∉ S, Work.NN.Final.seeleyTV a b δ g m =ᶠ[𝓝 p] 0) := by
  obtain ⟨M, hM⟩ := Work.NN.Final.exists_b_ge hbT (2 / (-(p.2 / 2)))
  have hp2 : p.2 < p.2 / 2 := by linarith
  have hneigh : {q : X × ℝ | q.2 < p.2 / 2} ∈ 𝓝 p :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hp2
  refine ⟨Finset.range M, ?_, ?_⟩
  · filter_upwards [hneigh] with q hq
    unfold Work.NN.Final.seeleySumV
    symm
    rw [tsum_eq_sum (s := Finset.range M)]
    intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    exact seeleyTV_eq_zero_of_lt hb δ g hM hm hp hq
  · intro m hm
    have hm' : M ≤ m := by simpa [Finset.mem_range, not_lt] using hm
    filter_upwards [hneigh] with q hq
    exact seeleyTV_eq_zero_of_lt hb δ g hM hm' hp hq

/-- The iterated derivative at a point only depends on the germ of the function. -/
lemma iteratedFDeriv_congr_of_eventuallyEq {f g : X × ℝ → ℂ} {x : X × ℝ}
    (h : f =ᶠ[𝓝 x] g) (k : ℕ) :
    iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k g x := by
  have h' : f =ᶠ[𝓝[Set.univ] x] g := by rwa [nhdsWithin_univ]
  have := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) h' h.eq_of_nhds k
  simpa only [iteratedFDerivWithin_univ] using this

/-- On the open lower half space the Seeley sum is locally a finite sum of the terms, so its
iterated derivatives are the termwise derivatives. -/
theorem iteratedFDeriv_seeleySumV_of_neg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {δ : ℝ} (hδ : 0 < δ) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2})
    (k : ℕ) {x : X × ℝ} (hx : x.2 < 0) :
    iteratedFDeriv ℝ k (Work.NN.Final.seeleySumV a b δ g) x
      = ∑' m, iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) x := by
  obtain ⟨S, hSfin, hSzero⟩ := exists_finset_seeleySumV_eventuallyEq hb hbT δ g hx
  have h1 : iteratedFDeriv ℝ k (Work.NN.Final.seeleySumV a b δ g) x
      = iteratedFDeriv ℝ k (fun q => ∑ m ∈ S, Work.NN.Final.seeleyTV a b δ g m q) x :=
    iteratedFDeriv_congr_of_eventuallyEq hSfin k
  have h2 : iteratedFDeriv ℝ k (fun q => ∑ m ∈ S, Work.NN.Final.seeleyTV a b δ g m q) x
      = ∑ m ∈ S, iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) x :=
    iteratedFDeriv_fun_sum_apply (fun m _ => (seeleyTV_contDiff hδ hg a b k m).contDiffAt)
  have h3 : ∑ m ∈ S, iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) x
      = ∑' m, iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) x := by
    refine (tsum_eq_sum (s := S)
      (f := fun m => iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) x) ?_).symm
    intro m hm
    have h0 := iteratedFDeriv_congr_of_eventuallyEq (hSzero m hm) k
    rw [h0]
    simp
  rw [h1, h2, h3]

end Work.NN.Seeley
