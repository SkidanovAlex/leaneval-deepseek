/-
  WilE9G / Assembly — the *box-free* Morse-genericity statement.

  `Work.WilE9G.Lagrange.exists_null_of_degenerate` proves the genericity statement under the
  additional hypothesis that the Lagrange point `z` lies in the *open* cube (`∀ i, |z i| < 1`).
  That hypothesis is never used by its proof: the underlying Sard-on-a-level-set argument
  (`Work.WilE9G.Sard.sardOnLevelSet`) is global in the ambient space, and the only place the
  stratum is used is through `z ∈ S.X.set` (`Good`-locality, the equations and the rank
  condition).  Since `S.X.set ⊆ cubeC` gives only `|z i| ≤ 1`, the strict bound is not implied.

  This file re-runs that argument without the strict bound, giving the statement actually used in
  the assembly.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.exists_null_of_degenerate
import Submission.Work.WilE9G.Lagrange.Stratum

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

theorem exists_null_of_degenerate_all {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (hS : S.Good) (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r)
    (hPhi : ∀ z ∈ S.X.set, 0 < WilkiesDesign.E.eaEval S.X.c Phi z) :
    ∃ Nc : Set (Fin (1 + m) → ℝ), MeasureTheory.volume Nc = 0 ∧
      ∀ c : Fin (1 + m) → ℝ, c ∉ Nc → ∃ Nx : Set (Fin n → ℝ), MeasureTheory.volume Nx = 0 ∧
        ∀ x : Fin n → ℝ, x ∉ Nx →
          ∀ z : Fin (n + (1 + m)) → ℝ, z ∈ S.X.set →
            Work.WilE9G.projBase (Nat.le_add_right n (1 + m)) z = x →
            ∀ (mu : Fin S.j → ℝ) (mu0 : ℝ),
              Work.WilE9G.LagEq S Phi c z mu mu0 → Work.WilE9G.LagNorm mu mu0 →
              (Work.WilE9G.lagJac S Phi c z mu mu0).det ≠ 0 := by
  classical
  -- the null set `N₁` of the general Sard theorem
  obtain ⟨N₁, hN₁null, hN₁⟩ :=
    Work.WilE9G.Sard.exists_null_of_Good_amb (Nat.le_add_right n (1 + m)) S hS
  -- Sard on the level set, at each reference point
  have key : ∀ p : degenV S Phi, ∃ (N : Set (Fin (n + (1 + m)) → ℝ))
      (U : Set (Fin (degenDim n m S.j) → ℝ)),
      volume N = 0 ∧ U ∈ 𝓝 (p : Fin (degenDim n m S.j) → ℝ) ∧
        ∀ z ∈ U, degenH S Phi z = degenH S Phi p →
          (¬ ∀ w : Fin (n + (1 + m)) → ℝ, ∃ v : Fin (degenDim n m S.j) → ℝ,
            fderiv ℝ (degenH S Phi) z v = 0 ∧ fderiv ℝ (degenF S) z v = w) →
          degenF S z ∈ N := by
    intro p
    exact Work.WilE9G.Sard.sardOnLevelSet (degenH S Phi) (degenF S)
      (fun x => analyticAt_degenH S Phi x) (fun x => analyticAt_degenF S x)
      (p : Fin (degenDim n m S.j) → ℝ)
      (degenH_fderiv_surjective S hS Phi hPhi (p : Fin (degenDim n m S.j) → ℝ) p.2.1 p.2.2.2)
  choose N U hN hU hconcl using key
  -- countable subcover
  have hLind : IsLindelof (degenV S Phi) := by
    rw [isLindelof_iff_lindelofSpace]; infer_instance
  obtain ⟨t, htcount, htcover⟩ := hLind.elim_nhds_subcover'
    (fun (x : Fin (degenDim n m S.j) → ℝ) (hx : x ∈ degenV S Phi) => U ⟨x, hx⟩)
    (fun (x : Fin (degenDim n m S.j) → ℝ) (hx : x ∈ degenV S Phi) => hU ⟨x, hx⟩)
  -- the null set `N₂`
  set N₂ : Set (Fin (n + (1 + m)) → ℝ) := ⋃ x ∈ t, N x with hN₂def
  have hN₂null : volume N₂ = 0 := by
    rw [hN₂def]
    have heq : (⋃ x ∈ t, N x) = ⋃ x : (t : Set (degenV S Phi)), N x.1 := by
      ext w; constructor
      · intro hw
        obtain ⟨x, hx, hw⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hw⟩
      · intro hw
        obtain ⟨x, hw⟩ := Set.mem_iUnion.mp hw
        exact Set.mem_iUnion₂.mpr ⟨x.1, x.2, hw⟩
    rw [heq]
    haveI : Countable ↥t := htcount.to_subtype
    exact MeasureTheory.measure_iUnion_null_iff.mpr (fun x : t => hN x.1)
  -- the second null set (its slices are exactly `N₁`)
  set T : Set (Fin (n + (1 + m)) → ℝ) :=
    {w | projBase (Nat.le_add_right n (1 + m)) w ∈ N₁} with hTdef
  -- every degenerate Lagrange point gives a point of `N₂ ∪ T`
  have hBad_sub : ∀ (z : Fin (n + (1 + m)) → ℝ) (ν : Fin S.j → ℝ) (ν0 : ℝ)
      (c : Fin (1 + m) → ℝ), z ∈ S.X.set →
      LagEq S Phi c z ν ν0 → LagNorm ν ν0 → (lagJac S Phi c z ν ν0).det = 0 →
      Fin.append (projBase (Nat.le_add_right n (1 + m)) z) c ∈ N₂ ∪ T := by
    intro z ν ν0 c hz hEq hNorm hdet
    let p : Fin (degenDim n m S.j) → ℝ := degenPt z (degenNuMk S ν ν0) c
    have hpz : degenZ p = z := by simp only [p, degenZ_degenPt]
    have hpc : degenC p = c := by simp only [p, degenC_degenPt]
    have hpν : degenNuA S p = ν := by simp only [p, degenNuA_degenPt]
    have hpν0 : degenNu0 S p = ν0 := by simp only [p, degenNu0_degenPt]
    have hF : degenF S p = Fin.append (projBase (Nat.le_add_right n (1 + m)) z) c :=
      degenF_degenPt S z (degenNuMk S ν ν0) c
    have hH : degenH S Phi p = 0 := by
      funext i
      rw [degenH]
      revert i
      refine Fin.addCases ?_ ?_
      · intro a
        rw [Fin.append_left]
        show eaEval S.X.c (S.h a) (degenZ p) = 0
        rw [hpz]; exact AmbStratum_eq_zero S hS hz a
      · intro b
        rw [Fin.append_right]
        revert b
        refine Fin.addCases ?_ ?_
        · intro u
          rw [Fin.append_left]
          show degenLam S p = 0
          rw [degenLam, degenNu_degenPt, Fin.sum_univ_castSucc]
          have h2 : ∀ a : Fin S.j, (degenNuMk S ν ν0 (Fin.castSucc a)) ^ 2 = (ν a) ^ 2 :=
            fun a => by
              rw [show (Fin.castSucc a : Fin (S.j + 1)) = Fin.castAdd 1 a from Fin.ext rfl,
                degenNuMk_castAdd]
          rw [Finset.sum_congr rfl (fun a _ => h2 a), degenNuMk_last]
          have := hNorm
          simp only [LagNorm] at this
          linarith
        · intro l
          rw [Fin.append_right]
          show degenPsi S Phi p l = 0
          rw [degenPsi, degenNu_degenPt, degenC_degenPt, degenZ_degenPt]
          simp only [degenNuMk_castAdd, degenNuMk_last]
          have hh : ν0 * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) z
                + eaEval S.X.c Phi z * c l)
              = ∑ a : Fin S.j, ν a * eaEval S.X.c
                  (eaD S.X.c (Fin.natAdd n l) (S.h a)) z := hEq l
          rw [← hh]; ring
    have hdet' : (lagJac S Phi (degenC p) (degenZ p) (degenNuA S p) (degenNu0 S p)).det = 0 := by
      rw [hpc, hpz, hpν, hpν0]; exact hdet
    by_cases h0 : ν0 = 0
    · -- `ν₀ = 0`: the base point is base-critical
      right
      rw [hTdef]
      simp only [Set.mem_setOf_eq]
      rw [projBase_finAppend]
      have hsq : (∑ a : Fin S.j, (ν a) ^ 2) ≠ 0 := by
        intro h
        have := hNorm
        simp only [LagNorm] at this
        rw [h, zero_add, h0] at this
        norm_num at this
      have hker : ∀ l : Fin (1 + m),
          ∑ a, ν a * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) z = 0 := by
        intro l
        have hh := hEq l
        simp only [h0, zero_mul] at hh
        linarith [hh]
      exact hN₁ z hz (not_isBaseSubmersiveAt_of_fibre_kernel S hS z hz ν hsq hker)
    · -- `ν₀ ≠ 0`: the point is critical for `degenF` on the level set of `degenH`
      left
      have hpV : p ∈ degenV S Phi := ⟨by rw [hpz]; exact hz, hH, by rw [hpν0]; exact h0⟩
      obtain ⟨x, hx, hxU⟩ := Set.mem_iUnion₂.mp (htcover hpV)
      have hcrit := degen_not_cond_of_det_eq_zero S hS Phi hPhi p (by rw [hpz]; exact hz) hH
        (by rw [hpν0]; exact h0) hdet'
      have hheq : degenH S Phi p = degenH S Phi (x : Fin (degenDim n m S.j) → ℝ) := by
        rw [hH, x.2.2.1]
      have hmem := hconcl x p hxU hheq hcrit
      rw [← hF]
      exact Set.mem_iUnion₂.mpr ⟨x, hx, hmem⟩
  -- the bad set of `(x,c)` pairs
  set Bad : Set (Fin (n + (1 + m)) → ℝ) :=
    {w | ∃ (z : Fin (n + (1 + m)) → ℝ) (ν : Fin S.j → ℝ) (ν0 : ℝ) (c : Fin (1 + m) → ℝ),
      z ∈ S.X.set ∧ LagEq S Phi c z ν ν0 ∧ LagNorm ν ν0 ∧
      (lagJac S Phi c z ν ν0).det = 0 ∧
      w = Fin.append (projBase (Nat.le_add_right n (1 + m)) z) c} with hBaddef
  have hBad_sub2 : Bad ⊆ N₂ ∪ T := by
    intro w hw
    obtain ⟨z, ν, ν0, c, hz, hEq, hNorm, hdet, rfl⟩ := hw
    exact hBad_sub z ν ν0 c hz hEq hNorm hdet
  have hfub := Work.WilE9G.Fubini.ae_null_slice_of_null N₂ hN₂null
  refine ⟨{c : Fin (1 + m) → ℝ | ¬ volume {x : Fin n → ℝ | Fin.append x c ∈ N₂} = 0}, ?_, ?_⟩
  · exact MeasureTheory.ae_iff.mp hfub
  · intro c hc
    have hcN₂ : volume {x : Fin n → ℝ | Fin.append x c ∈ N₂} = 0 := by
      by_contra h; exact hc h
    refine ⟨{x : Fin n → ℝ | Fin.append x c ∈ Bad}, ?_, ?_⟩
    · have hset : {x : Fin n → ℝ | Fin.append x c ∈ Bad}
          ⊆ {x : Fin n → ℝ | Fin.append x c ∈ N₂} ∪ N₁ := by
        intro x hx
        rcases hBad_sub2 hx with h | h
        · exact Or.inl h
        · refine Or.inr ?_
          have h2 : projBase (Nat.le_add_right n (1 + m)) (Fin.append x c) ∈ N₁ := by
            simpa only [hTdef, Set.mem_setOf_eq] using h
          rwa [projBase_finAppend] at h2
      refine measure_mono_null hset ?_
      refine le_antisymm ?_ bot_le
      calc volume ({x : Fin n → ℝ | Fin.append x c ∈ N₂} ∪ N₁)
          ≤ volume {x : Fin n → ℝ | Fin.append x c ∈ N₂} + volume N₁ := measure_union_le _ _
        _ = 0 := by rw [hcN₂, hN₁null, add_zero]
    · intro x hx z hz hproj mu mu0 hEq hNorm
      by_contra hdet
      exact hx ⟨z, mu, mu0, c, hz, hEq, hNorm, hdet, by rw [hproj]⟩

end Work.WilE9G.Assembly
