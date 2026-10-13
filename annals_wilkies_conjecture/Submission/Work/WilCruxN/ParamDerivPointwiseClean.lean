import Mathlib
import Submission.Work.WilCruxN.PDPDefsClean
import Submission.Work.WilCruxN.PDPPathClean
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4b.ESet_mem
import Submission.Work.WilG4a.affine_comb_graph_mem
import Submission.Work.WilG1.Main
import Submission.Work.WilG1.Cell.thin_closure
import Submission.Work.WilG5.Basic
import Submission.Work.WilG4c.BadLocusThin
import Submission.Work.WilCrux.OmegaModulus
import Submission.Work.WilCrux.BaireDefinableCover
import Submission.Work.WilCrux.SphereChoice
import Submission.Work.WilCrux.UnifMonotonePieces
import Submission.Work.WilCrux.PathGainBound

namespace Work.WilCruxN

open Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-! ## 7. The main theorem -/

/-- **N4c (the parameter-direction step).**  For a definable family with `C^1` slices, jointly
`C^1` off the sheet, and with the slice derivative uniformly continuous at the sheet, the
parameter partials converge to the parameter partial of the sheet value `a(w) = G w 0`, off a set
with empty interior.

Proof shape (see `WilCrux/DESIGN.md`, N4c).  `Ĝ := G - a`, `a(w) := G w 0`.  The `Ω`-sets
`E := {(w,z) : z ≠ 0, ∂_{w_i}Ĝ(w,z) ≥ 1/k}` (via `derivGraph_mem`, restricted to the `C¹`-locus)
and their sign companions are used through:

1. if the failure set has interior, a ball `B` in it is covered by the `Ω`-sets
   `B⁺_k ∪ B⁻_k` (`B⁺_k` = "a gain `≥ 1/k` at arbitrarily small radii"), so
   `BaireDefinableCover` yields an open `Q₃ ⊆ B⁺_k` (split the signs using `thin_closure` if the
   mixed set is fat); shrink `Q₃` to the `C¹`-locus of `a`;
2. `SphereChoice` gives a definable `ζ(w,τ)` with `0 < ‖ζ w τ‖ ≤ τ` and the gain at `(w,ζ)`
   (`hacc`-style hypothesis of N4c2 is *automatic* from `B⁺_k`: for every `τ > 0` there is a
   witness of radius `≤ τ` at every `w ∈ Q₃`);
3. fix a segment `[w₁, w₁+L e_i] ⊆ Q₃` and set `ψ(s) := ζ(w₁+s e_i, τ)` (the `M`-bound for the
   slice derivative near the sheet follows from `hz` and `hsl`);
4. the coordinate functions `s ↦ ψ_k(s)` are definable one-variable functions, so by
   `UnifMonotonePieces` they are differentiable and monotone off a bounded set `brk`;
5. `PathGainBound` gives `(1/k)·L ≤ C·τ` for every `τ > 0`, a contradiction as `τ → 0`; hence
   the failure set has empty interior. -/
theorem ParamDerivPointwise (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {a b F D : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1))
    (Q0 : Set (Fin a → ℝ)) (hQ0 : IsOpen Q0) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q0, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hoff : ∀ w ∈ Q0, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (hz : ∀ w₀ ∈ Q0, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε)
    (i : Fin a) :
    interior {w : Fin a → ℝ | w ∈ Q0 ∧ ¬ Filter.Tendsto
      (fun z : Fin b → ℝ =>
        fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append (Pi.single i 1) 0)
          - fderiv ℝ (fun w' => G w' 0) w (Pi.single i 1))
      (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0)} = ∅ := by

  classical
  by_cases hb0 : b = 0
  · subst hb0
    have hpt : ({(0 : Fin 0 → ℝ)}ᶜ : Set (Fin 0 → ℝ)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact hx (Subsingleton.elim x 0)
    have hset : {w : Fin a → ℝ | w ∈ Q0 ∧ ¬ Filter.Tendsto
        (fun z : Fin 0 → ℝ =>
          fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append (Pi.single i 1) 0)
            - fderiv ℝ (fun w' => G w' 0) w (Pi.single i 1))
        (nhdsWithin (0 : Fin 0 → ℝ) {(0 : Fin 0 → ℝ)}ᶜ) (nhds 0)} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro w hw
      exact hw.2 (by rw [hpt, nhdsWithin_empty]; exact Filter.tendsto_bot)
    rw [hset, interior_empty]
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
  set Fail : Set (Fin a → ℝ) := {w : Fin a → ℝ | w ∈ Q0 ∧ ¬ Filter.Tendsto
      (fun z : Fin b → ℝ =>
        fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append (Pi.single i 1) 0)
          - fderiv ℝ (fun w' => G w' 0) w (Pi.single i 1))
      (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0)} with hFail
  by_contra hne
  obtain ⟨w₀, hw₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨ρ, hρ, hρball⟩ := (Metric.isOpen_iff.mp isOpen_interior) w₀ hw₀
  have hρsub : Metric.ball w₀ ρ ⊆ Fail := fun x hx => interior_subset (hρball hx)
  set sv : (Fin a → ℝ) → ℝ := fun w => G w 0 with hsv
  set Lam : Set (Fin a → ℝ) := {w : Fin a → ℝ | ContDiffAt ℝ 1 sv w} with hLam
  have hLamopen : IsOpen Lam := by
    rw [hLam]
    exact Work.WilkG4c.isOpen_contDiffAt_set (k := 1) sv
  obtain ⟨Fsh, Dsh, hshgraph⟩ := pdp_flatGraph_stub S (G := G) hG
  have hLamcompl : interior Lamᶜ = ∅ := by
    have h := WilkiesDesign.CG.G1_generic_smooth_proved S hcd sv hshgraph 1
    rw [hLam, Set.compl_ofPred]
    exact h
  have hQne : (Metric.ball w₀ ρ ∩ Lam).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : Metric.ball w₀ ρ ⊆ Lamᶜ := by
      intro x hx
      by_contra hxL
      have hx' : x ∈ Metric.ball w₀ ρ ∩ Lam := ⟨hx, not_not.mp hxL⟩
      rw [hcon] at hx'
      exact hx'
    have h1 : Metric.ball w₀ ρ ⊆ interior Lamᶜ := interior_maximal hsub Metric.isOpen_ball
    rw [hLamcompl] at h1
    exact h1 (by rw [Metric.mem_ball, dist_self]; exact hρ)
  set Q : Set (Fin a → ℝ) := Metric.ball w₀ ρ ∩ Lam with hQ
  have hQopen : IsOpen Q := by rw [hQ]; exact Metric.isOpen_ball.inter hLamopen
  have hQsub : Q ⊆ Fail := by
    intro x hx
    rw [hQ] at hx
    exact hρsub hx.1
  have hQsubQ0 : ∀ w ∈ Q, w ∈ Q0 := by
    intro w hw
    have h := hQsub hw
    rw [hFail] at h
    exact h.1
  -- the two signed families and their gain loci
  set Fp : (Fin a → ℝ) → (Fin b → ℝ) → ℝ := pdpHat G with hFp
  obtain ⟨Fph, Dph, hFphgraph⟩ := pdp_sheetHat_stub S (G := G) hG hshgraph
  have hFpgraph : WilkiesDesign.CG.famGraph Fp ∈ S.Ω Fph Dph (a + b + 1) := hFphgraph
  set Fn : (Fin a → ℝ) → (Fin b → ℝ) → ℝ := fun w z => -(Fp w z) with hFn
  obtain ⟨Fnh, Dnh, hFngraph⟩ := pdp_negGraph_mem S (Fam := Fp) hFpgraph
  obtain ⟨FpE, DpE, hpMem⟩ := pdp_gainSet_mem S hcd Fp hFpgraph i
  obtain ⟨FnE, DnE, hnMem⟩ := pdp_gainSet_mem S hcd Fn hFngraph i
  have hEpos : ∀ k : ℕ, pdpE Fp i (1 / ((k : ℝ) + 1)) ∈ S.Ω FpE DpE (a + b) :=
    fun k => hpMem _
  have hEneg : ∀ k : ℕ, pdpE Fn i (1 / ((k : ℝ) + 1)) ∈ S.Ω FnE DnE (a + b) :=
    fun k => hnMem _
  -- the cover of `Q` by the accumulation sets
  have hcover : Q ⊆ ⋃ k : ℕ, (pdpAcc (pdpE Fp i (1 / ((k : ℝ) + 1)))
      ∪ pdpAcc (pdpE Fn i (1 / ((k : ℝ) + 1)))) := by
    intro w hw
    rw [hQ] at hw
    obtain ⟨hwball, hwLam⟩ := hw
    rw [hLam] at hwLam
    have hwF := hQsub ⟨hwball, by rw [hLam]; exact hwLam⟩
    rw [hFail] at hwF
    obtain ⟨hwQ0, hwfail⟩ := hwF
    rw [pdp_not_tendsto_punctured_iff] at hwfail
    obtain ⟨ε, hεpos, hwit⟩ := hwfail
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hεpos
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    by_cases hpos : w ∈ pdpAcc (pdpE Fp i (1 / ((k : ℝ) + 1)))
    · exact Or.inl hpos
    refine Or.inr ?_
    rw [pdpAcc] at hpos ⊢
    simp only [Set.mem_ofPred_eq] at hpos
    obtain ⟨δ₁, hδ₁⟩ := not_forall.mp hpos
    have hδ₁pos : 0 < δ₁ := by
      by_contra hcon
      exact hδ₁ (fun h' => absurd h' hcon)
    have hδ₁no : ¬ ∃ z : Fin b → ℝ, 0 < ‖z‖ ∧ ‖z‖ < δ₁ ∧
        Fin.append w z ∈ pdpE Fp i (1 / ((k : ℝ) + 1)) := fun hex => hδ₁ (fun _ => hex)
    intro δ hδ
    obtain ⟨z, hz0, hzδ, hzε⟩ := hwit (min δ (min δ₁ r0)) (lt_min hδ (lt_min hδ₁pos hr0))
    have hzr : ‖z‖ < r0 := lt_of_lt_of_le hzδ (le_trans (min_le_right _ _) (min_le_right _ _))
    have hzδ₁ : ‖z‖ < δ₁ := lt_of_lt_of_le hzδ (le_trans (min_le_right _ _) (min_le_left _ _))
    have hzδ₀ : ‖z‖ < δ := lt_of_lt_of_le hzδ (min_le_left _ _)
    have hgood := pdp_hat_eq G i Q0 r0 hoff hwQ0 hwLam hz0 hzr
    have hc1 : Fin.append w z ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun Fp) := hgood.1
    have hid : fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)
          (Fin.append (Pi.single i 1) 0) - fderiv ℝ sv w (Pi.single i 1)
        = Work.WilG4b.dDir (Work.WilG4c.famFun Fp) (Fin.castAdd b i) (Fin.append w z) := hgood.2
    have hnot : Fin.append w z ∉ pdpE Fp i (1 / ((k : ℝ) + 1)) := fun hmem =>
      hδ₁no ⟨z, norm_pos_iff.mpr hz0, hzδ₁, hmem⟩
    have hvlt : Work.WilG4b.dDir (Work.WilG4c.famFun Fp) (Fin.castAdd b i) (Fin.append w z)
        < 1 / ((k : ℝ) + 1) := by
      by_contra hcon
      exact hnot (pdpE_mem.mpr ⟨hc1, not_lt.mp hcon⟩)
    have hDge : 1 / ((k : ℝ) + 1)
        ≤ |Work.WilG4b.dDir (Work.WilG4c.famFun Fp) (Fin.castAdd b i) (Fin.append w z)| := by
      rw [← hid]
      exact le_trans hk.le hzε
    refine ⟨z, norm_pos_iff.mpr hz0, hzδ₀, ?_⟩
    rw [pdpE_mem]
    refine ⟨?_, ?_⟩
    · rw [show Work.WilG4c.famFun Fn = fun u => -(Work.WilG4c.famFun Fp u) from rfl,
        pdp_c1Loc_neg]
      exact hc1
    · rw [show Work.WilG4c.famFun Fn = fun u => -(Work.WilG4c.famFun Fp u) from rfl,
        pdp_dDir_neg]
      have hle : Work.WilG4b.dDir (Work.WilG4c.famFun Fp) (Fin.castAdd b i) (Fin.append w z)
          ≤ -(1 / ((k : ℝ) + 1)) := by
        rcases le_or_gt 0 (Work.WilG4b.dDir (Work.WilG4c.famFun Fp) (Fin.castAdd b i)
          (Fin.append w z)) with h | h
        · rw [abs_of_nonneg h] at hDge
          exact absurd hDge (not_le.mpr hvlt)
        · rw [abs_of_neg h] at hDge
          linarith
      linarith
  -- first Baire step
  obtain ⟨k₀, hk₀⟩ := BaireDefinableCover S hcd
    (fun k : ℕ => pdpAcc (pdpE Fp i (1 / ((k : ℝ) + 1)))
      ∪ pdpAcc (pdpE Fn i (1 / ((k : ℝ) + 1))))
    (fun k => by
      obtain ⟨F1, D1, h1⟩ := pdp_accSet_stub S (pdpE Fp i (1 / ((k : ℝ) + 1))) (hEpos k)
      obtain ⟨F2, D2, h2⟩ := pdp_accSet_stub S (pdpE Fn i (1 / ((k : ℝ) + 1))) (hEneg k)
      exact ⟨max F1 F2, D1 + D2, pdp_union_mem h1 h2⟩)
    Q hQopen hQne hcover
  set Q₁ : Set (Fin a → ℝ) := interior (pdpAcc (pdpE Fp i (1 / ((k₀ : ℝ) + 1)))
    ∪ pdpAcc (pdpE Fn i (1 / ((k₀ : ℝ) + 1)))) ∩ Q with hQ₁
  have hQ₁open : IsOpen Q₁ := by rw [hQ₁]; exact isOpen_interior.inter hQopen
  have hQ₁ne : Q₁.Nonempty := hk₀
  have hQ₁sub : Q₁ ⊆ pdpAcc (pdpE Fp i (1 / ((k₀ : ℝ) + 1)))
      ∪ pdpAcc (pdpE Fn i (1 / ((k₀ : ℝ) + 1))) := by
    intro x hx
    rw [hQ₁] at hx
    exact interior_subset hx.1
  -- second Baire step: a uniform sign
  obtain ⟨n₂, hn₂⟩ := BaireDefinableCover S hcd
    (fun n : ℕ => if n = 0 then pdpAcc (pdpE Fp i (1 / ((k₀ : ℝ) + 1)))
      else pdpAcc (pdpE Fn i (1 / ((k₀ : ℝ) + 1))))
    (fun n => by
      by_cases hn : n = 0
      · subst hn
        obtain ⟨F1, D1, h1⟩ := pdp_accSet_stub S (pdpE Fp i (1 / ((k₀ : ℝ) + 1))) (hEpos k₀)
        exact ⟨F1, D1, by simpa using h1⟩
      · obtain ⟨F2, D2, h2⟩ := pdp_accSet_stub S (pdpE Fn i (1 / ((k₀ : ℝ) + 1))) (hEneg k₀)
        exact ⟨F2, D2, by simpa [hn] using h2⟩)
    Q₁ hQ₁open hQ₁ne (fun x hx => by
      rcases hQ₁sub hx with h | h
      · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩)
  set Q₂ : Set (Fin a → ℝ) := interior (if n₂ = 0 then pdpAcc (pdpE Fp i (1 / ((k₀ : ℝ) + 1)))
    else pdpAcc (pdpE Fn i (1 / ((k₀ : ℝ) + 1)))) ∩ Q₁ with hQ₂
  have hQ₂open : IsOpen Q₂ := by rw [hQ₂]; exact isOpen_interior.inter hQ₁open
  have hQ₂ne : Q₂.Nonempty := hn₂
  set Fs : (Fin a → ℝ) → (Fin b → ℝ) → ℝ := if n₂ = 0 then Fp else Fn with hFs
  set Es : Set (Fin (a + b) → ℝ) := pdpE Fs i (1 / ((k₀ : ℝ) + 1)) with hEs
  have hQ₂sub : Q₂ ⊆ pdpAcc Es := by
    intro x hx
    rw [hQ₂] at hx
    have h := interior_subset hx.1
    rw [hEs, hFs]
    by_cases hh : n₂ = 0
    · rw [if_pos hh] at h ⊢
      exact h
    · rw [if_neg hh] at h ⊢
      exact h
  have hEs_mem : Es ∈ S.Ω (max FpE FnE) (DpE + DnE) (a + b) := by
    rw [hEs, hFs]
    by_cases hh : n₂ = 0
    · rw [if_pos hh]
      exact Work.WilG1.Omega.mono (hEpos k₀) (le_max_left _ _) (Nat.le_add_right _ _)
    · rw [if_neg hh]
      exact Work.WilG1.Omega.mono (hEneg k₀) (le_max_right _ _) (Nat.le_add_left _ _)
  have hEs_c1 : ∀ u ∈ Es, ContDiffAt ℝ 1 (Work.WilG4c.famFun Fs) u :=
    fun u hu => pdp_c1Loc_iff.mp (pdpE_mem.mp hu).1
  have hEs_gain : ∀ u ∈ Es, 1 / ((k₀ : ℝ) + 1)
      ≤ Work.WilG4b.dDir (Work.WilG4c.famFun Fs) (Fin.castAdd b i) u :=
    fun u hu => (pdpE_mem.mp hu).2
  -- the definable choice function
  obtain ⟨ζ, Fz, bz, hζ, hζgraph⟩ := SphereChoice S hcd Es hEs_mem
  -- geometric setup along a segment
  obtain ⟨w₁, hw₁⟩ := hQ₂ne
  have hw₁Q : w₁ ∈ Q := by
    rw [hQ₂, hQ₁] at hw₁
    exact hw₁.2.2
  have hw₁Q0 : w₁ ∈ Q0 := hQsubQ0 w₁ hw₁Q
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := (Metric.isOpen_iff.mp hQ₂open) w₁ hw₁
  obtain ⟨η₁, hη₁pos, hη₁⟩ := hz w₁ hw₁Q0 1 one_pos
  obtain ⟨z₀, hz₀ne, hz₀norm⟩ : ∃ z₀ : Fin b → ℝ, z₀ ≠ 0 ∧ ‖z₀‖ < min η₁ r0 := by
    refine ⟨(min η₁ r0 / 2) • (Pi.single (⟨0, hbpos⟩ : Fin b) 1 : Fin b → ℝ), ?_, ?_⟩
    · intro hcon
      have h1 : ((min η₁ r0 / 2) • (Pi.single (⟨0, hbpos⟩ : Fin b) 1 : Fin b → ℝ))
          ⟨0, hbpos⟩ = 0 := by rw [hcon]; rfl
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1
      have h2 : 0 < min η₁ r0 / 2 := by positivity
      linarith
    · have hnorm : ‖(min η₁ r0 / 2) • (Pi.single (⟨0, hbpos⟩ : Fin b) 1 : Fin b → ℝ)‖
          = min η₁ r0 / 2 := by
        rw [norm_smul, Pi.norm_single, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          Real.norm_eq_abs, abs_one, mul_one]
      rw [hnorm]
      have h3 : 0 < min η₁ r0 := lt_min hη₁pos hr0
      linarith
  have hz₀r0 : ‖z₀‖ < r0 := lt_of_lt_of_le hz₀norm (min_le_right _ _)
  have hz₀η₁ : ‖z₀‖ < η₁ := lt_of_lt_of_le hz₀norm (min_le_left _ _)
  have hC1z₀ : ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w₁ z₀) :=
    hoff w₁ hw₁Q0 z₀ hz₀ne hz₀r0
  have hcontfd : ContinuousAt (fun u : Fin (a + b) → ℝ =>
      fderiv ℝ (Work.WilG4c.famFun G) u) (Fin.append w₁ z₀) :=
    hC1z₀.continuousAt_fderiv (by norm_num)
  have hcontcomp : ContinuousAt (fun w : Fin a → ℝ =>
      fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z₀)) w₁ :=
    by
      have hg : ContinuousAt (fun w : Fin a → ℝ => Fin.append w z₀) w₁ :=
        (((Fin.continuous_append (X := ℝ) a b).comp
          (continuous_id.prodMk continuous_const))).continuousAt
      exact ContinuousAt.comp (f := fun w : Fin a → ℝ => Fin.append w z₀) hcontfd hg
  obtain ⟨δc, hδc, hδc'⟩ := Metric.continuousAt_iff.mp hcontcomp 1 one_pos
  set M : ℝ := ‖fderiv ℝ (G w₁) z₀‖ + 3 with hMdef
  have hM : 0 ≤ M := by rw [hMdef]; positivity
  set m : ℝ := min (min ρ₂ δc) η₁ with hm
  have hmpos : 0 < m := lt_min (lt_min hρ₂ hδc) hη₁pos
  set L : ℝ := m / 2 with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  set τ₀ : ℝ := min m r0 / 2 with hτ₀
  have hτ₀pos : 0 < τ₀ := by rw [hτ₀]; positivity
  have hτ₀m : τ₀ ≤ m := by
    rw [hτ₀]
    have h := min_le_left m r0
    linarith
  have hτ₀r0 : τ₀ ≤ r0 := by
    rw [hτ₀]
    have h := min_le_right m r0
    linarith
  have hτ₀η₁ : τ₀ ≤ η₁ := by
    refine le_trans hτ₀m ?_
    exact min_le_right (min ρ₂ δc) η₁
  have hnorm_shift : ∀ s : ℝ, ‖(w₁ + s • Pi.single i 1) - w₁‖ = |s| := by
    intro s
    have h1 : ‖(Pi.single i (1 : ℝ) : Fin a → ℝ)‖ = 1 := by
      rw [Pi.norm_single, Real.norm_eq_abs, abs_one]
    rw [add_sub_cancel_left, norm_smul, h1, mul_one, Real.norm_eq_abs]
  have hQ₂Q : Q₂ ⊆ Q := by
    intro x hx
    rw [hQ₂] at hx
    rw [hQ₁] at hx
    exact hx.2.2
  have hτ₀ltr0 : τ₀ < r0 := by
    rw [hτ₀]
    have h2 : min m r0 ≤ r0 := min_le_right m r0
    linarith
  have hτ₀ltη₁ : τ₀ < η₁ := by
    rw [hτ₀]
    have h2 : m ≤ η₁ := by rw [hm]; exact min_le_right _ η₁
    have h1 : min m r0 ≤ m := min_le_left m r0
    linarith
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) L, w₁ + s • Pi.single i 1 ∈ Q₂ := by
    intro s hs
    apply hρ₂sub
    rw [Metric.mem_ball, dist_eq_norm, hnorm_shift]
    have hsabs : |s| ≤ L := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
    have hmρ : m ≤ ρ₂ := le_trans (min_le_left _ _) (min_le_left _ _)
    rw [hL] at hsabs
    linarith
  -- derivative bound along the segment
  have hnorm_pi_append : ∀ v : Fin b → ℝ, ‖Fin.append (0 : Fin a → ℝ) v‖ ≤ ‖v‖ := by
    intro v
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
    intro j
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) j
    · rw [Fin.append_left]; simp
    · rw [Fin.append_right]; exact norm_le_pi_norm v j'
  have htri : ∀ x y : (Fin b → ℝ) →L[ℝ] ℝ, ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    intro x y
    have h := norm_add_le (x - y) y
    rwa [sub_add_cancel] at h
  have hderiv_bound : ∀ s ∈ Set.Icc (0 : ℝ) L, ∀ z : Fin b → ℝ, ‖z‖ ≤ τ₀ →
      ‖fderiv ℝ (G (w₁ + s • Pi.single i 1)) z‖ ≤ M := by
    intro s hs z hz
    have hws : w₁ + s • Pi.single i 1 ∈ Q0 := hQsubQ0 _ (hQ₂Q (hseg s hs))
    have hsabs : |s| ≤ L := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
    have hdist : dist (w₁ + s • Pi.single i 1) w₁ < min η₁ δc := by
      rw [dist_eq_norm, hnorm_shift]
      have hmη : m ≤ η₁ := by rw [hm]; exact min_le_right _ η₁
      have hmδ : m ≤ δc := by
        rw [hm]
        exact le_trans (min_le_left _ η₁) (min_le_right ρ₂ δc)
      rw [hL] at hsabs
      exact lt_min (by linarith) (by linarith)
    have hdistη : dist (w₁ + s • Pi.single i 1) w₁ < η₁ :=
      lt_of_lt_of_le hdist (min_le_left _ _)
    have hdistδ : dist (w₁ + s • Pi.single i 1) w₁ < δc :=
      lt_of_lt_of_le hdist (min_le_right _ _)
    have hA : ‖fderiv ℝ (G (w₁ + s • Pi.single i 1)) 0
        - fderiv ℝ (G (w₁ + s • Pi.single i 1)) z₀‖ < 1 := by
      have hd := hη₁ _ _ hdistη hz₀ne hz₀η₁
      rwa [norm_sub_rev] at hd
    have hC : ‖fderiv ℝ (G (w₁ + s • Pi.single i 1)) z₀ - fderiv ℝ (G w₁) z₀‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v => ?_)
      have h1 := Work.WilCrux.fibreFderivFamFun G (w₁ + s • Pi.single i 1) z₀ v
        (hoff _ hws z₀ hz₀ne hz₀r0).differentiableAt_one
      have h2 := Work.WilCrux.fibreFderivFamFun G w₁ z₀ v
        (hoff w₁ hw₁Q0 z₀ hz₀ne hz₀r0).differentiableAt_one
      have h3 : ‖fderiv ℝ (Work.WilG4c.famFun G) (Fin.append (w₁ + s • Pi.single i 1) z₀)
          - fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w₁ z₀)‖ < 1 := by
        have hd := hδc' hdistδ
        rwa [dist_eq_norm] at hd
      have h1' : fderiv ℝ (G (w₁ + s • Pi.single i 1)) z₀
          = (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append (w₁ + s • Pi.single i 1) z₀)).comp
              (Work.WilCrux.fibreIncl a b) := by
        ext u
        rw [ContinuousLinearMap.comp_apply, Work.WilCrux.fibreIncl_apply]
        exact (Work.WilCrux.fibreFderivFamFun G (w₁ + s • Pi.single i 1) z₀ u
          (hoff _ hws z₀ hz₀ne hz₀r0).differentiableAt_one).symm
      have h2' : fderiv ℝ (G w₁) z₀
          = (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w₁ z₀)).comp
              (Work.WilCrux.fibreIncl a b) := by
        ext u
        rw [ContinuousLinearMap.comp_apply, Work.WilCrux.fibreIncl_apply]
        exact (Work.WilCrux.fibreFderivFamFun G w₁ z₀ u
          (hoff w₁ hw₁Q0 z₀ hz₀ne hz₀r0).differentiableAt_one).symm
      calc ‖(fderiv ℝ (G (w₁ + s • Pi.single i 1)) z₀ - fderiv ℝ (G w₁) z₀) v‖
          = ‖((fderiv ℝ (Work.WilG4c.famFun G) (Fin.append (w₁ + s • Pi.single i 1) z₀)
              - fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w₁ z₀)).comp
                (Work.WilCrux.fibreIncl a b)) v‖ := by
            rw [h1', h2', ← ContinuousLinearMap.sub_comp]
        _ = ‖(fderiv ℝ (Work.WilG4c.famFun G) (Fin.append (w₁ + s • Pi.single i 1) z₀)
              - fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w₁ z₀)) (Fin.append 0 v)‖ := by
            rw [ContinuousLinearMap.comp_apply, Work.WilCrux.fibreIncl_apply]
        _ ≤ ‖fderiv ℝ (Work.WilG4c.famFun G) (Fin.append (w₁ + s • Pi.single i 1) z₀)
              - fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w₁ z₀)‖ * ‖Fin.append 0 v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖v‖ :=
            mul_le_mul (le_of_lt h3) (hnorm_pi_append v) (norm_nonneg _) (by norm_num)
    have hAB : ‖fderiv ℝ (G (w₁ + s • Pi.single i 1)) z₀
        - fderiv ℝ (G (w₁ + s • Pi.single i 1)) 0‖
        = ‖fderiv ℝ (G (w₁ + s • Pi.single i 1)) 0
        - fderiv ℝ (G (w₁ + s • Pi.single i 1)) z₀‖ := norm_sub_rev _ _
    by_cases hz0' : z = 0
    · subst hz0'
      linarith [htri (fderiv ℝ (G (w₁ + s • Pi.single i 1)) 0)
          (fderiv ℝ (G (w₁ + s • Pi.single i 1)) z₀),
        htri (fderiv ℝ (G (w₁ + s • Pi.single i 1)) z₀) (fderiv ℝ (G w₁) z₀),
        le_of_lt hA, hC, hAB, hMdef]
    · have hB : ‖fderiv ℝ (G (w₁ + s • Pi.single i 1)) z
          - fderiv ℝ (G (w₁ + s • Pi.single i 1)) 0‖ < 1 :=
        hη₁ _ _ hdistη hz0' (lt_of_le_of_lt hz hτ₀ltη₁)
      linarith [htri (fderiv ℝ (G (w₁ + s • Pi.single i 1)) z)
          (fderiv ℝ (G (w₁ + s • Pi.single i 1)) 0),
        htri (fderiv ℝ (G (w₁ + s • Pi.single i 1)) 0)
          (fderiv ℝ (G (w₁ + s • Pi.single i 1)) z₀),
        htri (fderiv ℝ (G (w₁ + s • Pi.single i 1)) z₀) (fderiv ℝ (G w₁) z₀),
        le_of_lt hB, le_of_lt hA, hC, hAB, hMdef]
  have hdiffball : ∀ s ∈ Set.Icc (0 : ℝ) L, ∀ z ∈ Metric.closedBall (0 : Fin b → ℝ) τ₀,
      DifferentiableAt ℝ (G (w₁ + s • Pi.single i 1)) z := by
    intro s hs z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    have hsub : Metric.closedBall (0 : Fin b → ℝ) τ₀ ⊆ Metric.ball 0 r0 := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact lt_of_le_of_lt hx hτ₀ltr0
    exact ((hsl _ (hQsubQ0 _ (hQ₂Q (hseg s hs)))).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub (by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hz)))).differentiableAt_one
  -- the Lipschitz / smallness bounds for the signed family
  have hFs_lip_fun : ∀ (w : Fin a → ℝ) (z z' : Fin b → ℝ),
      |Fs w z - Fs w z'| = |G w z - G w z'| := by
    intro w z z'
    have h2 : Fp w z - Fp w z' = G w z - G w z' := by
      rw [hFp]; simp only [pdpHat]; ring
    rw [hFs]
    by_cases hh : n₂ = 0
    · rw [if_pos hh, h2]
    · rw [if_neg hh]
      have h1 : Fn w z - Fn w z' = -(Fp w z - Fp w z') := by rw [hFn]; ring
      rw [h1, h2, abs_neg]
  have hFs_small_fun : ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      |Fs w z| = |G w z - G w 0| := by
    intro w z
    have h2 : Fp w z = G w z - G w 0 := by
      rw [hFp]; simp only [pdpHat]
    rw [hFs]
    by_cases hh : n₂ = 0
    · rw [if_pos hh, h2]
    · rw [if_neg hh]
      have h1 : Fn w z = -(Fp w z) := by rw [hFn]
      rw [h1, h2, abs_neg]
  -- the monotone pieces of the coordinate functions along the line
  have hηkpos : 0 < 1 / ((k₀ : ℝ) + 1) := by positivity
  obtain ⟨K, hKbound⟩ := pdp_path_step (S := S) (hcd := hcd) (G := G) (i := i)
    (Fs := Fs) (ζ := ζ) (Es := Es) (Q₂ := Q₂) (Fz := Fz) (bz := bz) (D := DpE + DnE)
    hζgraph w₁ L τ₀ M (1 / ((k₀ : ℝ) + 1)) r0 hηkpos hLpos hτ₀pos hr0 hM hτ₀r0
    hseg hQ₂sub hEs_gain hEs_c1 hζ hdiffball hderiv_bound hFs_lip_fun hFs_small_fun
  -- final contradiction: let `τ → 0`
  set Cb : ℝ := ((↑K : ℝ) + 2) * (2 * ((b : ℝ) + 1) * M + 1) with hCb
  have hCbpos : 0 < Cb := by
    rw [hCb]
    have h1 : (0 : ℝ) ≤ (↑K : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ M := hM
    have h3 : (0 : ℝ) < 2 * ((b : ℝ) + 1) * M + 1 := by positivity
    have h4 : (0 : ℝ) ≤ 2 * ((b : ℝ) + 1) * M + 1 := le_of_lt h3
    positivity
  set τc : ℝ := min (τ₀ / 2) (1 / ((k₀ : ℝ) + 1) * L / (2 * Cb)) with hτc
  have hτcpos : 0 < τc := by
    rw [hτc]
    refine lt_min (by linarith) ?_
    have : 0 < 1 / ((k₀ : ℝ) + 1) := by positivity
    positivity
  have hτcτ₀ : τc < τ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hbnd := hKbound τc ⟨hτcpos, hτcτ₀⟩
  have hle : τc ≤ 1 / ((k₀ : ℝ) + 1) * L / (2 * Cb) := min_le_right _ _
  have hmul : Cb * τc ≤ Cb * (1 / ((k₀ : ℝ) + 1) * L / (2 * Cb)) :=
    mul_le_mul_of_nonneg_left hle hCbpos.le
  have hsimp : Cb * (1 / ((k₀ : ℝ) + 1) * L / (2 * Cb)) = 1 / ((k₀ : ℝ) + 1) * L / 2 := by
    field_simp
  have hpos : 0 < 1 / ((k₀ : ℝ) + 1) * L := by positivity
  linarith [hbnd, hmul, hsimp.symm.le, hsimp.le]


end Work.WilCruxN
