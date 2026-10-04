import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.pdVec_gard_defect_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local Leibniz bound for the iterated partial derivatives `pdVec`

The requested target is `Work.Diff.STE.Lead.Gal.gardLeibnizLocal` (statement unchanged, see below).
It is the *local* (germ) version of the product bound: the two factors are only assumed
`ContDiffAt` (smooth at the single point `z`), which is what the transport application needs
(the weight `ψ_j√dens_j` and the chart matrix are smooth only near the `2σ`-ball).

## Route

The proof is self-contained (it does not import the module `...Gal.pdVec_mul_bound`, whose source
does not currently compile).  The three ingredients are:

* **Germ independence** (`pdList_eventuallyEq`, `pdVec_eventuallyEq`): functions which agree near
  `z` have the same iterated partial derivatives at `z`.  This is the induction
  `Filter.EventuallyEq.fderiv` (the *eventual* form of the congruence of `fderiv`) followed by
  `Filter.EventuallyEq.eq_of_nhds`.
* **The global product bound** `pdVec_mul_bound_contDiff`, proved by copying the proof of the
  global `pdVec_mul_bound` (`pdList_mul_sub` + the split bookkeeping `cm_splits_length_count`,
  `cm_splits_mem_length` + the list-sum bounds), with the differentiability hypotheses obtained
  from `ContDiff ℝ (N+1)` via `cm_contDiff_pdList`.  The `ContDiff` index needed is only the
  finite order `N+1` (for the globalised functions below), not `⊤`.
* **Globalisation of a locally smooth function** (`contDiff_mul_bump`): if `f` is `C^M` on an
  open set `U` and `g` has closed support in `U`, then `f · g` is globally `C^M`
  (the same argument as in `Work.Diff.STE.B3.contDiff_mul_of_tsupport_subset`, adapted to
  complex-valued `f`).

Given `hF : ContDiffAt ℝ ∞ F z` we extract an open neighbourhood `U_F ∋ z` on which `F` is
`C^{N+1}` (via `contDiffWithinAt_nat` and `HasFTaylorSeriesUpToOn.contDiffOn`), pick a bump `ρ`
which is `≡ 1` near `z` and has closed support in `U_F ∩ U_G`, and set `F' := ρ · F`, `G' := ρ · G`.
Then `F'`, `G'` are globally `C^{N+1}`, agree with `F`, `G` near `z`, and so do `F'G'` and `FG`;
the germ independence transfers the jet bounds back and forth.
-/

noncomputable section

namespace Work.Diff.STE.Lead.Gal

open scoped BigOperators ContDiff Topology

/-! ## 1. Germ independence of the iterated partial derivatives -/

/-- The iterated partial derivatives only depend on the germ at `z`. -/
private lemma pdList_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι] {z : ι → ℝ}
    {f g : (ι → ℝ) → ℂ} (h : f =ᶠ[𝓝 z] g) (q : List ι) :
    Work.Diff.STE.pdList q f =ᶠ[𝓝 z] Work.Diff.STE.pdList q g := by
  induction q with
  | nil => simpa only [Work.Diff.STE.pdList, List.foldr_nil] using h
  | cons i q ih =>
      have h' : Work.Diff.STE.pd i (Work.Diff.STE.pdList q f) =ᶠ[𝓝 z]
          Work.Diff.STE.pd i (Work.Diff.STE.pdList q g) := by
        filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
        simp only [Work.Diff.STE.pd, hy]
      simpa only [Work.Diff.STE.pdList, List.foldr_cons] using h'

/-- The value at `z` of any iterated partial derivative only depends on the germ at `z`. -/
private lemma pdVec_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι] {z : ι → ℝ}
    {f g : (ι → ℝ) → ℂ} (h : f =ᶠ[𝓝 z] g) (m : ℕ) (β : Fin m → ι) :
    Work.Diff.STE.pdVec m β f z = Work.Diff.STE.pdVec m β g z := by
  rw [Work.Diff.STE.pdVec]
  exact (pdList_eventuallyEq h (List.ofFn β)).eq_of_nhds

/-! ## 2. Globalising a locally smooth function -/

/-- If `f` is `C^M` on an open set `U` and the closed support of `g` lies in `U`, then the product
`f · g` (with `g` complexified) is globally `C^M`.  This is the complex-valued analogue of
`Work.Diff.STE.B3.contDiff_mul_of_tsupport_subset`. -/
private lemma contDiff_mul_bump {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U) {M : ℕ}
    {f : (Fin n → ℝ) → ℂ} {g : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ((M : ℕ) : WithTop ℕ∞) f U)
    (hg : ContDiff ℝ ((M : ℕ) : WithTop ℕ∞) g) (hsupp : tsupport g ⊆ U) :
    ContDiff ℝ ((M : ℕ) : WithTop ℕ∞) (fun z => f z * ((g z : ℝ) : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · have hgc : ContDiffAt ℝ ((M : ℕ) : WithTop ℕ∞) (fun y => ((g y : ℝ) : ℂ)) z := by
      have h1 : ContDiffAt ℝ ((M : ℕ) : WithTop ℕ∞) (⇑Complex.ofRealCLM) (g z) :=
        (Complex.ofRealCLM.contDiff (n := ((M : ℕ) : WithTop ℕ∞))).contDiffAt (x := g z)
      have h3 : ContDiffAt ℝ ((M : ℕ) : WithTop ℕ∞) (⇑Complex.ofRealCLM ∘ g) z :=
        h1.comp z hg.contDiffAt
      convert h3 using 1
      ext y
      simp only [Complex.ofRealCLM_apply, Function.comp_apply]
    exact (hf.contDiffAt (hU.mem_nhds hz)).mul hgc
  · have hz' : z ∉ tsupport g := fun h => hz (hsupp h)
    have hnear : g =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hz'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with y hy
    rw [hy, Complex.ofReal_zero, mul_zero]

/-! ## 3. The global product bound -/

/-- Every iterated partial derivative of a `C^M` function of order `≤ M-1` is differentiable. -/
private lemma differentiable_pdList_of_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℂ} {M : ℕ} (hf : ContDiff ℝ ((M : ℕ) : WithTop ℕ∞) f) {q : List ι}
    (hq : q.length + 1 ≤ M) : Differentiable ℝ (Work.Diff.STE.pdList q f) :=
  (Work.Diff.STE.cm_contDiff_pdList q 1 f (Work.Diff.STE.cm_of_le hf (by simpa using hq)))
    |>.differentiable (by norm_num)

/-- **Product bound for the iterated partial derivatives at a point** (global `C^{N+1}` version).

This is the global product bound of `pdVec_mul_bound`, with the smoothness hypotheses weakened from
`ContDiff ℝ ⊤` to `ContDiff ℝ (N+1)` (which is all that is needed for orders `≤ N`) and with a
self-contained proof. -/
private theorem pdVec_mul_bound_contDiff {n N : ℕ} {z : Fin n → ℝ} {F G : (Fin n → ℝ) → ℂ}
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ContDiff ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) F)
    (hG : ContDiff ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) G)
    (hFz : ∀ (j : ℕ), j ≤ N → ∀ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ F z‖ ≤ A)
    (hGz : ∀ (j : ℕ), j ≤ N → ∀ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ G z‖ ≤ B) :
    ∀ (j : ℕ), j ≤ N → ∀ γ : Fin j → Fin n,
      ‖Work.Diff.STE.pdVec j γ (fun y => F y * G y) z‖
        ≤ (2 : ℝ) ^ (N + 1) * (A + 1) * (B + 1) := by
  intro j hj γ
  classical
  set l : List (Fin n) := List.ofFn γ with hl
  have hlen : l.length = j := by rw [hl]; exact List.length_ofFn
  set L : List (List (Fin n) × List (Fin n)) :=
    (Work.Diff.STE.splits l).filter (fun p : List (Fin n) × List (Fin n) => p.1 ≠ []) with hL
  -- the iterated Leibniz rule, in difference form
  have hleib := Work.Diff.STE.pdList_mul_sub l F G
    (fun q _ hq => differentiable_pdList_of_contDiff hF (by rw [hlen] at hq; omega))
    (fun q _ hq => differentiable_pdList_of_contDiff hG (by rw [hlen] at hq; omega))
  have hz := congrFun hleib z
  -- the Leibniz defect identity
  have hFG : Work.Diff.STE.pdVec j γ (fun y => F y * G y) z
      = (L.map (fun p => Work.Diff.STE.pdList p.1 F z
            * Work.Diff.STE.pdList p.2 G z)).sum + F z * Work.Diff.STE.pdList l G z := by
    rw [Work.Diff.STE.pdVec, ← hl]
    simpa only [hL] using sub_eq_iff_eq_add.mp hz
  -- the bound on `F z`
  have hFz0 : ‖F z‖ ≤ A := by
    have h := hFz 0 (Nat.zero_le N) (Fin.elim0 : Fin 0 → Fin n)
    rwa [pdVec_zero_gal] at h
  -- the bound on `∂^l G`
  have hGl : ‖Work.Diff.STE.pdList l G z‖ ≤ B := by
    rw [pdList_eq_pdVec_gal]
    exact hGz l.length (by omega) (fun i : Fin l.length => l.get i)
  -- the bound on every term of the defect sum
  have hterm : ∀ p ∈ L, ‖Work.Diff.STE.pdList p.1 F z * Work.Diff.STE.pdList p.2 G z‖
      ≤ A * B := by
    intro p hp
    rw [hL] at hp
    obtain ⟨hp', hne⟩ := List.mem_filter.mp hp
    have hne' : p.1 ≠ [] := of_decide_eq_true hne
    have hlen' := Work.Diff.STE.cm_splits_mem_length l p hp'
    have h1 : p.1.length ≤ N := by
      have := List.length_pos_of_ne_nil hne'
      omega
    have h2 : p.2.length ≤ N := by omega
    rw [norm_mul]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) hA
    · rw [pdList_eq_pdVec_gal]
      exact hFz p.1.length h1 (fun i : Fin p.1.length => p.1.get i)
    · rw [pdList_eq_pdVec_gal]
      exact hGz p.2.length h2 (fun i : Fin p.2.length => p.2.get i)
  -- the combinatorial bound: at most `2^j ≤ 2^N` terms
  have hcount : (L.length : ℝ) ≤ 2 ^ N := by
    have h2 : L.length ≤ (Work.Diff.STE.splits l).length := by
      rw [hL]; exact List.length_filter_le _ _
    rw [Work.Diff.STE.cm_splits_length_count, hlen] at h2
    have h2' : (2 : ℕ) ^ j ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hj
    exact_mod_cast le_trans h2 h2'
  have hS : ‖(L.map (fun p => Work.Diff.STE.pdList p.1 F z
        * Work.Diff.STE.pdList p.2 G z)).sum‖ ≤ (L.length : ℝ) * (A * B) :=
    norm_list_sum_le_mul_gal L _ (A * B) hterm
  -- arithmetic
  have hAB : A * B ≤ (A + 1) * (B + 1) := by nlinarith [hA, hB]
  have hAB0 : 0 ≤ A * B := mul_nonneg hA hB
  have hpow : (1 : ℝ) + 2 ^ N ≤ 2 ^ (N + 1) := by
    calc (1 : ℝ) + 2 ^ N ≤ 2 ^ N + 2 ^ N := by
          have h1 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
          linarith
      _ = 2 ^ (N + 1) := by rw [pow_succ]; ring
  -- assembly
  rw [hFG]
  calc ‖(L.map (fun p => Work.Diff.STE.pdList p.1 F z
          * Work.Diff.STE.pdList p.2 G z)).sum
        + F z * Work.Diff.STE.pdList l G z‖
      ≤ ‖(L.map (fun p => Work.Diff.STE.pdList p.1 F z
            * Work.Diff.STE.pdList p.2 G z)).sum‖
          + ‖F z * Work.Diff.STE.pdList l G z‖ := norm_add_le _ _
    _ ≤ (L.length : ℝ) * (A * B) + A * B :=
        add_le_add hS (by rw [norm_mul]; exact mul_le_mul hFz0 hGl (norm_nonneg _) hA)
    _ = A * B * (1 + (L.length : ℝ)) := by ring
    _ ≤ A * B * (1 + 2 ^ N) :=
        mul_le_mul_of_nonneg_left (by linarith) hAB0
    _ ≤ A * B * 2 ^ (N + 1) := mul_le_mul_of_nonneg_left hpow hAB0
    _ ≤ (A + 1) * (B + 1) * 2 ^ (N + 1) :=
        mul_le_mul_of_nonneg_right hAB (by positivity)
    _ = (2 : ℝ) ^ (N + 1) * (A + 1) * (B + 1) := by ring

/-! ## 4. The local statement -/

/-- **Local Leibniz bound for the iterated partial derivatives `pdVec`.**

This is the local (germ) version of the proved `Work.Diff.STE.Lead.Gal.pdVec_mul_bound`, which
requires *global* smoothness of the two factors; here only `ContDiffAt ℝ ⊤` at the point `z` is
assumed, which is what the transport application needs (the weight `ψ_j√dens_j` and the chart
matrix are smooth only near the `2σ`-ball).  The recommended route: copy the proof of
`pdVec_mul_bound` (it uses the Leibniz expansion `Work.Diff.STE.pdList_mul_sub`, the split
bookkeeping `cm_splits_length_count`, and `norm_list_sum_le_mul_gal`), replacing the global
differentiability of the iterated derivatives by the local facts obtained from `ContDiffAt`
(equivalently: multiply both factors by a smooth bump `≡ 1` near `z` supported in a neighbourhood
where they are smooth, apply the global `pdVec_mul_bound`, and observe that the `pdVec` jets at `z`
of the products agree with those of the original factors). -/
theorem gardLeibnizLocal {n N : ℕ} {F G : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) F z)
    (hG : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) G z)
    (hFz : ∀ (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
      ‖Work.Diff.STE.pdVec m β F z‖ ≤ A)
    (hGz : ∀ (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
      ‖Work.Diff.STE.pdVec m β G z‖ ≤ B) :
    ∀ (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
      ‖Work.Diff.STE.pdVec m β (fun y => F y * G y) z‖
        ≤ (2 : ℝ) ^ (N + 1) * (A + 1) * (B + 1) := by
  intro m hm β
  -- `F` and `G` are `C^{N+1}` at `z`
  have hFn : ContDiffAt ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) F z :=
    hF.of_le (WithTop.coe_le_coe.mpr le_top)
  have hGn : ContDiffAt ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) G z :=
    hG.of_le (WithTop.coe_le_coe.mpr le_top)
  -- open neighbourhoods on which they are `C^{N+1}`
  obtain ⟨UF, hUF, pF, hpF⟩ := contDiffWithinAt_nat.mp hFn
  obtain ⟨UG, hUG, pG, hpG⟩ := contDiffWithinAt_nat.mp hGn
  have hUF' : UF ∈ 𝓝 z := by simpa using hUF
  have hUG' : UG ∈ 𝓝 z := by simpa using hUG
  have hzUF : z ∈ interior UF := mem_interior_iff_mem_nhds.mpr hUF'
  have hzUG : z ∈ interior UG := mem_interior_iff_mem_nhds.mpr hUG'
  have hOnF : ContDiffOn ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) F (interior UF) :=
    hpF.contDiffOn.mono interior_subset
  have hOnG : ContDiffOn ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) G (interior UG) :=
    hpG.contDiffOn.mono interior_subset
  -- a ball around `z` inside both
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (isOpen_interior.mem_nhds hzUF) (isOpen_interior.mem_nhds hzUG))
  -- the bump
  let ρ : ContDiffBump z := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hρtsup : tsupport (⇑ρ) ⊆ interior UF ∩ interior UG := by
    have h : tsupport (⇑ρ) = Metric.closedBall z (ε / 2) := ρ.tsupport_eq
    rw [h]
    exact subset_trans (Metric.closedBall_subset_ball (by linarith)) hball
  have hρsuppF : tsupport (⇑ρ) ⊆ interior UF := hρtsup.trans Set.inter_subset_left
  have hρsuppG : tsupport (⇑ρ) ⊆ interior UG := hρtsup.trans Set.inter_subset_right
  have hρsm : ContDiff ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) (⇑ρ) :=
    ρ.contDiff (n := ((N + 1 : ℕ) : ℕ∞))
  -- globalised factors
  set F' : (Fin n → ℝ) → ℂ := fun y => F y * ((ρ y : ℝ) : ℂ) with hF'def
  set G' : (Fin n → ℝ) → ℂ := fun y => G y * ((ρ y : ℝ) : ℂ) with hG'def
  have hF'sm : ContDiff ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) F' := by
    rw [hF'def]
    exact contDiff_mul_bump isOpen_interior hOnF hρsm hρsuppF
  have hG'sm : ContDiff ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) G' := by
    rw [hG'def]
    exact contDiff_mul_bump isOpen_interior hOnG hρsm hρsuppG
  -- they agree with the original factors near `z`
  have hF'eq : F' =ᶠ[𝓝 z] F := by
    rw [hF'def]
    filter_upwards [ρ.eventuallyEq_one] with y hy
    simp only [hy, Pi.one_apply, Complex.ofReal_one, mul_one]
  have hG'eq : G' =ᶠ[𝓝 z] G := by
    rw [hG'def]
    filter_upwards [ρ.eventuallyEq_one] with y hy
    simp only [hy, Pi.one_apply, Complex.ofReal_one, mul_one]
  -- the jet bounds transfer to the globalised factors
  have hF'z : ∀ (j : ℕ), j ≤ N → ∀ γ : Fin j → Fin n,
      ‖Work.Diff.STE.pdVec j γ F' z‖ ≤ A := by
    intro j hj γ
    rw [pdVec_eventuallyEq hF'eq j γ]
    exact hFz j hj γ
  have hG'z : ∀ (j : ℕ), j ≤ N → ∀ γ : Fin j → Fin n,
      ‖Work.Diff.STE.pdVec j γ G' z‖ ≤ B := by
    intro j hj γ
    rw [pdVec_eventuallyEq hG'eq j γ]
    exact hGz j hj γ
  -- the global bound for the globalised factors
  have hkey := pdVec_mul_bound_contDiff (n := n) (N := N) (z := z) hA hB hF'sm hG'sm hF'z hG'z
    m hm β
  -- the products agree near `z`, so their jets agree
  have hprodeq : (fun y => F' y * G' y) =ᶠ[𝓝 z] fun y => F y * G y := by
    filter_upwards [hF'eq, hG'eq] with y h1 h2
    rw [h1, h2]
  rw [← pdVec_eventuallyEq hprodeq m β]
  exact hkey

end Work.Diff.STE.Lead.Gal
