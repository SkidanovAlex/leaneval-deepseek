import Mathlib
import Submission.Work.Noncompact.CompressionTube.ctc.transverse_open
import Submission.Work.Noncompact.CompressionTube.ctc.exists_transverse_blend
import Submission.Work.Noncompact.CompressionTube.ctc.exists_local_transverse_piece
import Submission.Work.Noncompact.CompressionTube.ctc.isLocalDiffeomorphAt_pair_of_mfderiv_injective
import Submission.Work.Noncompact.CompressionTube.ctc.exists_gauge
import Submission.Work.Noncompact.CompressionTube.ctc.exists_finite_piece_cover
import Submission.Work.Compat.MFDerivCongrV433

/-!
# A transverse coordinate on a compact interval of a properly embedded line

Given a smooth proper embedding `γ : ℝ → M` of a line into a smooth `n`-manifold (`n ≥ 2`) and a
smooth `g : M → ℝ` with `g (γ s) = s` (so that `γ` is a leaf of the foliation `g = const`), we
produce, for every compact interval `[a,b]`, a *global* smooth `ψ : M → ℝ^{n-1}` vanishing on the
line and transverse to `g` at every point `γ s`, `s ∈ [a,b]`.

The construction is an induction along the interval:

* `exists_finite_piece_cover` gives finitely many *raw pieces* `ψ t` (each transverse on a
  neighbourhood `(t - rr t, t + rr t)` of `t`) whose "middle intervals"
  `(t - rr t/2, t + rr t/2)` cover `[a,b]`;
* `exists_gauge` aligns a fresh raw piece to the piece already constructed at the current right end
  `c` of the interval traversed so far: there is an injective linear `A` with
  `A ∘ dψ c = dΨ c`;
* `exists_transverse_blend` then shows that *any* `[0,1]`-valued blend
  `χ(g ·) • Ψ + (1 - χ(g ·)) • (A ∘ ψ)` is transverse in a window `|s - c| < ρb` around `c`,
  so using a smooth step `χ` that is `1` to the left of `c - ρb/4` and `0` to the right of
  `c + ρb/4` produces a new piece which is transverse on `[a, min (t + rr t/2) b]`
  (`extension_step`);
* the greedy chain of right ends `c k`, `c (k+1) = min (t k + rr (t k)/2) b`, terminates after at
  most `F.card` steps because the fresh index `t k` can never repeat while `c k < b`
  (`chain_card_eq_b`), and running `extension_step` along this chain produces the desired `ψ`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function Filter

noncomputable section

/-! ## Elementary helper lemmas -/

set_option backward.isDefEq.respectTransparency false in
/-- `Transverse γ g ψ s` depends only on the germ of `ψ` at `γ s`. -/
theorem transverse_congr {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} {g : M → ℝ} {ψ ψ' : M → EuclideanSpace ℝ (Fin (n - 1))} {s : ℝ}
    (h : ψ =ᶠ[𝓝 (γ s)] ψ') : Transverse γ g ψ s ↔ Transverse γ g ψ' s := by
  have hd : mfderiv (MC n) (MC (n - 1)) ψ (γ s) = mfderiv (MC n) (MC (n - 1)) ψ' (γ s) :=
    Filter.EventuallyEq.mfderiv_eq_v433 h
  constructor
  · intro hT v hv1 hv2
    refine hT v ?_ hv2
    rw [hd]
    exact hv1
  · intro hT v hv1 hv2
    refine hT v ?_ hv2
    rw [← hd]
    exact hv1

set_option backward.isDefEq.respectTransparency false in
/-- The chain rule for a continuous linear map precomposed with a smooth map: the manifold
derivative of `x ↦ A (ψ x)` is `A ∘ dψ`. -/
theorem mfderiv_clm_comp {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ)
    (A : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1))) (x : M) :
    mfderiv (MC n) (MC (n - 1)) (fun y => A (ψ y)) x =
      A.comp (mfderiv (MC n) (MC (n - 1)) ψ x) := by
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hψd : MDifferentiableAt (MC n) (MC (n - 1)) ψ x := hψ.mdifferentiableAt hn0
  exact ((ContinuousLinearMap.hasMFDerivAt A).comp x hψd.hasMFDerivAt).mfderiv

set_option backward.isDefEq.respectTransparency false in
/-- Application form of `mfderiv_clm_comp`. -/
theorem mfderiv_clm_comp_apply {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ)
    (A : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1))) (x : M)
    (v : TangentSpace (MC n) x) :
    mfderiv (MC n) (MC (n - 1)) (fun y => A (ψ y)) x v =
      A (mfderiv (MC n) (MC (n - 1)) ψ x v) := by
  have h := congrArg
    (fun (L : TangentSpace (MC n) x →L[ℝ] EuclideanSpace ℝ (Fin (n - 1))) => L v)
    (mfderiv_clm_comp hψ A x)
  change mfderiv (MC n) (MC (n - 1)) (fun y => A (ψ y)) x v =
    A (mfderiv (MC n) (MC (n - 1)) ψ x v) at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A smooth step function: identically `1` on `(-∞, c - η]`, identically `0` on `[c + η, ∞)` and
everywhere in `[0,1]`. -/
theorem exists_smoothStep (c η : ℝ) (hη : 0 < η) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ smoothOrder χ ∧ (∀ t : ℝ, χ t ∈ Set.Icc 0 1) ∧
      (∀ t : ℝ, t ≤ c - η → χ t = 1) ∧ (∀ t : ℝ, c + η ≤ t → χ t = 0) := by
  refine ⟨fun t => Real.smoothTransition ((c + η - t) / (2 * η)), ?_, ?_, ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_const.sub contDiff_id).div_const (2 * η))
  · intro t
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro t ht
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ (by linarith)]
    linarith
  · intro t ht
    refine Real.smoothTransition.zero_of_nonpos ?_
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-! ## The extension step -/

set_option backward.isDefEq.respectTransparency false in
/-- **The extension step.**  If `Ψ` is transverse on `[a,c]` (with `c ∈ [a,b]`) and `ψ` is a fresh
piece transverse on the interval `|t - s| < ρ` with `|c - s| < ρ/2`, then there is a piece `Ψ'`,
vanishing on the line, which is transverse on `[a, min (s + ρ/2) b]`. -/
theorem extension_step {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g) (hgcore : ∀ s : ℝ, g (γ s) = s)
    {a b c : ℝ} (hc : c ∈ Set.Icc a b) {Ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hΨsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ) (hΨ0 : ∀ t : ℝ, Ψ (γ t) = 0)
    (hΨT : ∀ t ∈ Set.Icc a c, Transverse γ g Ψ t)
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ) (hψ0 : ∀ t : ℝ, ψ (γ t) = 0)
    {s ρ : ℝ} (hρ : 0 < ρ) (hψT : ∀ t : ℝ, |t - s| < ρ → Transverse γ g ψ t)
    (hcU : |c - s| < ρ / 2) :
    ∃ Ψ' : M → EuclideanSpace ℝ (Fin (n - 1)),
      ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ' ∧ (∀ t : ℝ, Ψ' (γ t) = 0) ∧
      ∀ t ∈ Set.Icc a (min (s + ρ / 2) b), Transverse γ g Ψ' t := by
  classical
  have hcT : Transverse γ g Ψ c := hΨT c ⟨hc.1, le_refl c⟩
  have hcψ : Transverse γ g ψ c :=
    hψT c (by rw [abs_lt] at hcU ⊢; constructor <;> linarith)
  -- the gauge aligning the fresh piece to the current one
  obtain ⟨A, hAinj, hAeq⟩ := exists_gauge hn hγ hg hgcore hΨsm hψsm hΨ0 hψ0 c hcT hcψ
  have hGsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder (fun x : M => A (ψ x)) :=
    A.contMDiff.comp hψsm
  have hG0 : ∀ t : ℝ, (fun x : M => A (ψ x)) (γ t) = 0 := by
    intro t
    simp [hψ0 t]
  have hGder : mfderiv (MC n) (MC (n - 1)) (fun x : M => A (ψ x)) (γ c) =
      mfderiv (MC n) (MC (n - 1)) Ψ (γ c) := by
    ext v : 1
    rw [mfderiv_clm_comp_apply hψsm A (γ c) v]
    exact hAeq v
  -- the blend window
  obtain ⟨ρb, hρb, hblend⟩ := exists_transverse_blend hn hγ hinj hprop himm hg hgcore
    hΨsm hGsm hΨ0 hG0 hGder.symm hcT
  -- the step function
  obtain ⟨χ, hχsm, hχ01, hχ1, hχ0⟩ := exists_smoothStep c (ρb / 4) (by linarith)
  -- the fresh piece is transverse wherever `ψ` is
  have hGtrans' : ∀ t : ℝ, Transverse γ g ψ t → Transverse γ g (fun x : M => A (ψ x)) t := by
    intro t ht v hv1 hv2
    rw [mfderiv_clm_comp_apply hψsm A (γ t) v] at hv1
    exact ht v (hAinj (by simpa using hv1)) hv2
  refine ⟨fun x : M => χ (g x) • Ψ x + (1 - χ (g x)) • A (ψ x), ?_, ?_, ?_⟩
  · -- smoothness
    have h1 : ContMDiff (MC n) MCreal smoothOrder (fun x : M => χ (g x)) :=
      (contMDiff_iff_contDiff.mpr hχsm).comp hg
    have h2 : ContMDiff (MC n) MCreal smoothOrder (fun x : M => 1 - χ (g x)) :=
      contMDiff_const.sub h1
    exact (h1.smul hΨsm).add (h2.smul hGsm)
  · -- vanishing on the line
    intro t
    simp [hgcore t, hΨ0 t, hψ0 t]
  · -- transversality
    intro t ht
    have hts : t ≤ s + ρ / 2 := le_trans ht.2 (min_le_left _ _)
    by_cases h1 : t < c - ρb / 4
    · -- to the left of the window: `Ψ' = Ψ`
      have htc : t ∈ Set.Icc a c := ⟨ht.1, by linarith⟩
      have heq : (fun x : M => χ (g x) • Ψ x + (1 - χ (g x)) • A (ψ x)) =ᶠ[𝓝 (γ t)] Ψ := by
        have hop : {x : M | g x < c - ρb / 4} ∈ 𝓝 (γ t) :=
          hg.continuous.continuousAt.preimage_mem_nhds
            (by rw [hgcore t]; exact isOpen_Iio.mem_nhds h1)
        filter_upwards [hop] with x hx
        rw [hχ1 (g x) (le_of_lt hx)]
        simp
      exact (transverse_congr heq).mpr (hΨT t htc)
    · by_cases h2 : c + ρb / 4 < t
      · -- to the right of the window: `Ψ' = A ∘ ψ`
        have heq : (fun x : M => χ (g x) • Ψ x + (1 - χ (g x)) • A (ψ x)) =ᶠ[𝓝 (γ t)]
            (fun x : M => A (ψ x)) := by
          have hop : {x : M | c + ρb / 4 < g x} ∈ 𝓝 (γ t) :=
            hg.continuous.continuousAt.preimage_mem_nhds
              (by rw [hgcore t]; exact isOpen_Ioi.mem_nhds h2)
          filter_upwards [hop] with x hx
          rw [hχ0 (g x) (le_of_lt hx)]
          simp
        refine (transverse_congr heq).mpr (hGtrans' t (hψT t ?_))
        rw [abs_lt] at hcU ⊢
        constructor <;> linarith [hcU.1, hcU.2, hts, hρb, hρ, h2]
      · -- inside the window: the blend lemma
        have hmid : |t - c| < ρb := by
          rw [abs_lt]
          constructor <;> linarith
        exact hblend χ hχsm hχ01 t hmid

/-! ## The greedy chain of right ends

Given the finite list `F` of *raw pieces* from `exists_finite_piece_cover` (together with their
transversality radii `rr`), we build the chain of parameters `c k` at which the induction of
`extension_step` is performed: `c 0 = a` and, as long as `c k < b`, the next right end is the right
end `t + rr t/2` of the middle interval of a piece covering `c k`, capped at `b`.  The chain
reaches `b` in at most `F.card` steps, because the covering index `chainIdx k` cannot repeat while
the chain stays below `b`. -/

section Chain

variable {a b : ℝ} {F : Finset ℝ} {rr : ℝ → ℝ}

/-- The element of the finite cover whose middle interval contains `c`. -/
def coverIdx (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (c : ℝ) (hc : c ∈ Set.Icc a b) : ℝ :=
  Classical.choose (Set.mem_iUnion₂.mp (hcover hc))

theorem coverIdx_spec (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (c : ℝ) (hc : c ∈ Set.Icc a b) :
    coverIdx hcover c hc ∈ F ∧
      c ∈ Set.Ioo (coverIdx hcover c hc - rr (coverIdx hcover c hc) / 2)
        (coverIdx hcover c hc + rr (coverIdx hcover c hc) / 2) := by
  obtain ⟨h1, h2⟩ := Classical.choose_spec (Set.mem_iUnion₂.mp (hcover hc))
  exact ⟨h1, h2⟩

/-- The admissible right ends of the chain. -/
abbrev ChainPt (a b : ℝ) := {c : ℝ // c ∈ Set.Icc a b}

/-- The next right end: the right end of the middle interval of a piece covering `x`, capped at
`b`; the chain stops (stays at `b`) once it reaches `b`. -/
def nextEnd (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) (x : ChainPt a b) : ChainPt a b :=
  if x.val = b then ⟨b, ⟨hab, le_refl b⟩⟩
  else
    ⟨min (coverIdx hcover x.val x.property + rr (coverIdx hcover x.val x.property) / 2) b,
      ⟨le_min (le_trans x.property.1
          (le_of_lt (coverIdx_spec hcover x.val x.property).2.2)) hab, min_le_right _ _⟩⟩

/-- The greedy chain of right ends, starting at `a`. -/
def rightEnds (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) : ℕ → ChainPt a b
  | 0 => ⟨a, ⟨le_refl a, hab⟩⟩
  | k + 1 => nextEnd hcover hab (rightEnds hcover hab k)

/-- The index of the piece used at step `k` of the chain. -/
def chainIdx (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) (k : ℕ) : ℝ :=
  coverIdx hcover (rightEnds hcover hab k).val (rightEnds hcover hab k).property

theorem chainIdx_mem (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) (k : ℕ) : chainIdx hcover hab k ∈ F :=
  (coverIdx_spec hcover _ _).1

theorem chainIdx_spec (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) (k : ℕ) :
    (rightEnds hcover hab k).val ∈
      Set.Ioo (chainIdx hcover hab k - rr (chainIdx hcover hab k) / 2)
        (chainIdx hcover hab k + rr (chainIdx hcover hab k) / 2) :=
  (coverIdx_spec hcover _ _).2

theorem rightEnds_zero (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) : (rightEnds hcover hab 0).val = a := rfl

theorem rightEnds_succ (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) (k : ℕ) :
    (rightEnds hcover hab (k + 1)).val =
      if (rightEnds hcover hab k).val = b then b
      else min (chainIdx hcover hab k + rr (chainIdx hcover hab k) / 2) b := by
  rw [show rightEnds hcover hab (k + 1) = nextEnd hcover hab (rightEnds hcover hab k) from rfl]
  unfold nextEnd
  by_cases h : (rightEnds hcover hab k).val = b
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    simp [chainIdx]

theorem rightEnds_le_b (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) (k : ℕ) : (rightEnds hcover hab k).val ≤ b :=
  (rightEnds hcover hab k).property.2

theorem rightEnds_ge_a (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) (k : ℕ) : a ≤ (rightEnds hcover hab k).val :=
  (rightEnds hcover hab k).property.1

theorem rightEnds_step_le
    (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) (k : ℕ) :
    (rightEnds hcover hab k).val ≤ (rightEnds hcover hab (k + 1)).val := by
  rw [rightEnds_succ]
  by_cases h : (rightEnds hcover hab k).val = b
  · rw [if_pos h, h]
  · rw [if_neg h]
    exact le_min (le_of_lt (chainIdx_spec hcover hab k).2) (rightEnds_le_b hcover hab k)

theorem rightEnds_mono (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) : ∀ k l : ℕ, k ≤ l →
      (rightEnds hcover hab k).val ≤ (rightEnds hcover hab l).val := by
  intro k l hkl
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact le_trans ih (rightEnds_step_le hcover hab l)

/-- The covering indices used along the chain are pairwise distinct as long as the chain stays
below `b`. -/
theorem chainIdx_ne (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) {k l : ℕ} (hkl : k < l)
    (hk : (rightEnds hcover hab k).val < b) (hl : (rightEnds hcover hab l).val < b) :
    chainIdx hcover hab k ≠ chainIdx hcover hab l := by
  intro heq
  set A : ℝ := chainIdx hcover hab k + rr (chainIdx hcover hab k) / 2 with hA
  have hsucc : (rightEnds hcover hab (k + 1)).val = min A b := by
    rw [rightEnds_succ, if_neg (ne_of_lt hk), hA]
  have hmono : (rightEnds hcover hab (k + 1)).val ≤ (rightEnds hcover hab l).val :=
    rightEnds_mono hcover hab (k + 1) l (by omega)
  have hspec : (rightEnds hcover hab l).val ∈
      Set.Ioo (chainIdx hcover hab l - rr (chainIdx hcover hab l) / 2)
        (chainIdx hcover hab l + rr (chainIdx hcover hab l) / 2) := chainIdx_spec hcover hab l
  rw [Set.mem_Ioo] at hspec
  rw [← heq, ← hA] at hspec
  have hltA : min A b < A := lt_of_le_of_lt (le_of_eq hsucc.symm) (lt_of_le_of_lt hmono hspec.2)
  have hltb : min A b < b := lt_of_le_of_lt (le_of_eq hsucc.symm) (lt_of_le_of_lt hmono hl)
  rcases lt_or_ge A b with hcase | hcase
  · rw [min_eq_left (le_of_lt hcase)] at hltA
    exact lt_irrefl _ hltA
  · rw [min_eq_right hcase] at hltb
    exact lt_irrefl _ hltb

/-- **The chain reaches `b`** after at most `F.card` steps. -/
theorem rightEnds_card_eq_b
    (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2))
    (hab : a ≤ b) : (rightEnds hcover hab F.card).val = b := by
  by_contra hne
  have hltM : (rightEnds hcover hab F.card).val < b :=
    lt_of_le_of_ne (rightEnds_le_b hcover hab F.card) hne
  have hlt : ∀ k ≤ F.card, (rightEnds hcover hab k).val < b := fun k hk =>
    lt_of_le_of_lt (rightEnds_mono hcover hab k F.card hk) hltM
  have hinj : Set.InjOn (chainIdx hcover hab) ↑(Finset.range (F.card + 1)) := by
    intro k hk l hl hkl
    have hk' : k ≤ F.card := by have := Finset.mem_range.mp hk; omega
    have hl' : l ≤ F.card := by have := Finset.mem_range.mp hl; omega
    rcases lt_trichotomy k l with h | h | h
    · exact absurd hkl (chainIdx_ne hcover hab h (hlt k hk') (hlt l hl'))
    · exact h
    · exact absurd hkl.symm (chainIdx_ne hcover hab h (hlt l hl') (hlt k hk'))
  have hcard : ((Finset.range (F.card + 1)).image (chainIdx hcover hab)).card = F.card + 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : (Finset.range (F.card + 1)).image (chainIdx hcover hab) ⊆ F := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, -, rfl⟩
    exact chainIdx_mem hcover hab k
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  omega

end Chain

/-- **The induction along the chain.**  For every `k` there is a piece, vanishing on the line, which
is transverse on `[a, c k]`, where `c k` is the `k`-th right end of the greedy chain. -/
theorem exists_piece_on_chain {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g) (hgcore : ∀ s : ℝ, g (γ s) = s)
    {a b : ℝ} (hab : a ≤ b) {F : Finset ℝ} {rr : ℝ → ℝ}
    {psi : ℝ → M → EuclideanSpace ℝ (Fin (n - 1))}
    (hpieces : ∀ t ∈ F, ContMDiff (MC n) (MC (n - 1)) smoothOrder (psi t) ∧
      (∀ s : ℝ, psi t (γ s) = 0) ∧ 0 < rr t ∧
      ∀ s : ℝ, |s - t| < rr t → Transverse γ g (psi t) s)
    (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2)) (k : ℕ) :
    ∃ Ψ : M → EuclideanSpace ℝ (Fin (n - 1)),
      ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ ∧ (∀ s : ℝ, Ψ (γ s) = 0) ∧
      ∀ s ∈ Set.Icc a (rightEnds hcover hab k).val, Transverse γ g Ψ s := by
  induction k with
  | zero =>
      obtain ⟨hpsm, hp0, hρ, hpT⟩ := hpieces _ (chainIdx_mem hcover hab 0)
      refine ⟨psi (chainIdx hcover hab 0), hpsm, hp0, ?_⟩
      intro s hs
      have hsa : s = a := le_antisymm (by rw [rightEnds_zero] at hs; exact hs.2) hs.1
      rw [hsa]
      refine hpT a ?_
      have hspec : a ∈ Set.Ioo (chainIdx hcover hab 0 - rr (chainIdx hcover hab 0) / 2)
          (chainIdx hcover hab 0 + rr (chainIdx hcover hab 0) / 2) := by
        simpa [rightEnds_zero] using chainIdx_spec hcover hab 0
      rw [Set.mem_Ioo] at hspec
      rw [abs_lt]
      constructor <;> linarith
  | succ k ih =>
      obtain ⟨Ψ, hΨsm, hΨ0, hΨT⟩ := ih
      by_cases hkb : (rightEnds hcover hab k).val = b
      · refine ⟨Ψ, hΨsm, hΨ0, ?_⟩
        intro s hs
        rw [rightEnds_succ, if_pos hkb, ← hkb] at hs
        exact hΨT s hs
      · obtain ⟨hpsm, hp0, hρ, hpT⟩ := hpieces _ (chainIdx_mem hcover hab k)
        have hc : (rightEnds hcover hab k).val ∈ Set.Icc a b := (rightEnds hcover hab k).property
        have hmid : |(rightEnds hcover hab k).val - chainIdx hcover hab k| <
            rr (chainIdx hcover hab k) / 2 := by
          have hspec : (rightEnds hcover hab k).val ∈
              Set.Ioo (chainIdx hcover hab k - rr (chainIdx hcover hab k) / 2)
                (chainIdx hcover hab k + rr (chainIdx hcover hab k) / 2) :=
            chainIdx_spec hcover hab k
          rw [Set.mem_Ioo] at hspec
          rw [abs_lt]
          constructor <;> linarith
        obtain ⟨Ψ', hΨ'sm, hΨ'0, hΨ'T⟩ := extension_step hn hγ hinj hprop himm hg hgcore hc
          hΨsm hΨ0 hΨT hpsm hp0 hρ hpT hmid
        refine ⟨Ψ', hΨ'sm, hΨ'0, ?_⟩
        rw [rightEnds_succ, if_neg hkb]
        exact hΨ'T

set_option backward.isDefEq.respectTransparency false in
theorem exists_transverse_on_Icc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv
      Work.Noncompact.CompressionTube.MCreal (Work.Noncompact.CompressionTube.MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.MCreal Work.Noncompact.CompressionTube.smoothOrder g)
    (hgcore : ∀ s : ℝ, g (γ s) = s) (a b : ℝ) (hab : a ≤ b) :
    ∃ ψ : M → EuclideanSpace ℝ (Fin (n - 1)),
      ContMDiff (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC (n - 1))
        Work.Noncompact.CompressionTube.smoothOrder ψ ∧ (∀ s : ℝ, ψ (γ s) = 0) ∧
      ∀ s : ℝ, s ∈ Set.Icc a b →
        Work.Noncompact.CompressionTube.Transverse γ g ψ s := by
  obtain ⟨F, psi, rr, hpieces, hcover⟩ :=
    exists_finite_piece_cover hn hγ hinj hprop himm hg hgcore a b
  obtain ⟨Ψ, hΨsm, hΨ0, hΨT⟩ :=
    exists_piece_on_chain hn hγ hinj hprop himm hg hgcore hab hpieces hcover F.card
  refine ⟨Ψ, hΨsm, hΨ0, ?_⟩
  intro s hs
  exact hΨT s (by rw [rightEnds_card_eq_b hcover hab]; exact hs)

end

end Work.Noncompact.CompressionTube
