import Mathlib
import Submission.Work.Topology.tendsto_invSucc_nat_eventually_const

open MeasureTheory Set Topology Filter
open scoped Topology

namespace Work.Topology

/-- The canonical encoding of a natural number as a point of `[0,1]`. -/
noncomputable def encNat (m : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨((m : ℝ) + 1)⁻¹, by
    refine ⟨by positivity, ?_⟩
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    calc ((m : ℝ) + 1)⁻¹ = 1 / ((m : ℝ) + 1) := by rw [one_div]
      _ ≤ 1 / 1 := one_div_le_one_div_of_le (by norm_num) h1
      _ = 1 := by norm_num⟩

@[simp] lemma encNat_coe (m : ℕ) : ((encNat m : Set.Icc (0 : ℝ) 1) : ℝ) = ((m : ℝ) + 1)⁻¹ :=
  rfl

lemma encNat_ne_zero (m : ℕ) : ((encNat m : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0 := by
  rw [encNat_coe]; positivity

lemma continuous_encNat : Continuous encNat := continuous_of_discreteTopology

/-- The encoding of a sequence of naturals as a point of the Hilbert cube `ℕ → [0,1]`. -/
noncomputable def encSeq (x : ℕ → ℕ) : ℕ → Set.Icc (0 : ℝ) 1 := fun n => encNat (x n)

@[simp] lemma encSeq_apply (x : ℕ → ℕ) (n : ℕ) : encSeq x n = encNat (x n) := rfl

lemma continuous_encSeq : Continuous encSeq :=
  continuous_pi fun n => continuous_encNat.comp (continuous_apply n)

/-- There exists `k` with `1/(k+1) ≤ t` for every positive real `t`. -/
lemma exists_inv_succ_le {t : ℝ} (ht : 0 < t) : ∃ k : ℕ, ((k : ℝ) + 1)⁻¹ ≤ t := by
  obtain ⟨N, hN⟩ := exists_nat_ge (t⁻¹)
  have hNposR : (0 : ℝ) < N := lt_of_lt_of_le (inv_pos.mpr ht) hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by rintro h; rw [h] at hNposR; simp at hNposR)
  refine ⟨N - 1, ?_⟩
  have hNcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    rw [Nat.cast_sub hNpos, Nat.cast_one]; ring
  rw [hNcast]
  calc ((N : ℝ))⁻¹ = 1 / (N : ℝ) := by rw [one_div]
    _ ≤ 1 / (t⁻¹) := one_div_le_one_div_of_le (inv_pos.mpr ht) hN
    _ = t := by rw [one_div, inv_inv]

/-- The graph of a continuous map `g : ℕ^ℕ → α` inside `α × (ℕ → [0,1])`, closed up in the
Hilbert cube, together with the locus of points whose second coordinate has a nonzero
entry, gives back exactly the graph. -/
lemma closure_range_encSeq_inter {α : Type*} [TopologicalSpace α] [T2Space α] [PolishSpace α]
    {g : (ℕ → ℕ) → α} (hg : Continuous g) :
    closure (range (fun x : ℕ → ℕ => (g x, encSeq x))) ∩
        {p : α × (ℕ → Set.Icc (0 : ℝ) 1) | ∀ n, ((p.2 n : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0}
      = range (fun x : ℕ → ℕ => (g x, encSeq x)) := by
  apply Subset.antisymm
  · rintro p ⟨hpD, hpnz⟩
    rw [mem_closure_iff_seq_limit] at hpD
    obtain ⟨u, hu, hulim⟩ := hpD
    choose x hx using hu
    have hcoord : ∀ n, Tendsto (fun i => ((x i n : ℝ) + 1)⁻¹) atTop
        (𝓝 (((p.2 n : Set.Icc (0 : ℝ) 1) : ℝ))) := by
      intro n
      have h1 : Tendsto (fun i => (u i).2) atTop (𝓝 p.2) :=
        (continuous_snd.tendsto p).comp hulim
      have h2 : Tendsto (fun i => (u i).2 n) atTop (𝓝 (p.2 n)) :=
        ((continuous_apply n).tendsto (p.2)).comp h1
      have h3 : Tendsto (fun i => (((u i).2 n : Set.Icc (0 : ℝ) 1) : ℝ)) atTop
          (𝓝 (((p.2 n : Set.Icc (0 : ℝ) 1) : ℝ))) :=
        (continuous_subtype_val.tendsto _).comp h2
      refine h3.congr (fun i => ?_)
      rw [← hx i]
      rfl
    choose m hm using fun n => tendsto_invSucc_nat_eventually_const (hcoord n) (hpnz n)
    have hp2 : p.2 = encSeq m := by
      funext n
      exact Subtype.ext (hm n).1
    have hxlim : Tendsto x atTop (𝓝 m) := by
      rw [tendsto_pi_nhds]
      intro n
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(hm n).2] with i hi
      exact hi.symm
    have hglim : Tendsto (fun i => g (x i)) atTop (𝓝 (g m)) :=
      (hg.tendsto m).comp hxlim
    have hu1 : Tendsto (fun i => (u i).1) atTop (𝓝 p.1) :=
      (continuous_fst.tendsto p).comp hulim
    have hu1eq : (fun i => (u i).1) = (fun i => g (x i)) := by
      funext i; rw [← hx i]
    have hgm : g m = p.1 := tendsto_nhds_unique hglim (hu1eq ▸ hu1)
    exact ⟨m, Prod.ext hgm hp2.symm⟩
  · rintro p ⟨x, rfl⟩
    exact ⟨subset_closure (mem_range_self x), fun n => encNat_ne_zero (x n)⟩

theorem analyticSet_eq_iInter_iUnion_proj {α : Type*} [TopologicalSpace α] [T2Space α]
    [PolishSpace α] {S : Set α} (hS : MeasureTheory.AnalyticSet S) :
    ∃ E : ℕ → ℕ → Set (α × (ℕ → Set.Icc (0 : ℝ) 1)), (∀ n k, IsClosed (E n k)) ∧
      S = Prod.fst '' (⋂ n, ⋃ k, E n k) := by
  rw [MeasureTheory.AnalyticSet] at hS
  rcases hS with hS | ⟨g, hg, hgs⟩
  · subst hS
    exact ⟨fun _ _ => ∅, fun _ _ => isClosed_empty, by ext p; simp⟩
  · have hkey := closure_range_encSeq_inter (α := α) hg
    let F : ℕ → ℕ → Set (α × (ℕ → Set.Icc (0 : ℝ) 1)) := fun n k =>
      closure (range (fun x : ℕ → ℕ => (g x, encSeq x))) ∩
        {p : α × (ℕ → Set.Icc (0 : ℝ) 1) |
          ((k : ℝ) + 1)⁻¹ ≤ (((p.2 n : Set.Icc (0 : ℝ) 1)) : ℝ)}
    refine ⟨F, ?_, ?_⟩
    · intro n k
      have hcont : Continuous (fun p : α × (ℕ → Set.Icc (0 : ℝ) 1) =>
          (((p.2 n : Set.Icc (0 : ℝ) 1)) : ℝ)) :=
        continuous_subtype_val.comp ((continuous_apply n).comp continuous_snd)
      exact isClosed_closure.inter (IsClosed.preimage hcont isClosed_Ici)
    · have hInter : (⋂ n, ⋃ k, F n k)
          = closure (range (fun x : ℕ → ℕ => (g x, encSeq x))) ∩
            {p : α × (ℕ → Set.Icc (0 : ℝ) 1) |
              ∀ n, (((p.2 n : Set.Icc (0 : ℝ) 1)) : ℝ) ≠ 0} := by
        ext p
        simp only [F, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · intro hp
          refine ⟨(hp 0).choose_spec.1, fun n => ?_⟩
          obtain ⟨k, _, hk⟩ := hp n
          exact ne_of_gt (lt_of_lt_of_le (inv_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) one_pos)) hk)
        · rintro ⟨hpD, hpnz⟩ n
          have hpos : 0 < (((p.2 n : Set.Icc (0 : ℝ) 1)) : ℝ) :=
            lt_of_le_of_ne (p.2 n).2.1 (Ne.symm (hpnz n))
          obtain ⟨k, hk⟩ := exists_inv_succ_le hpos
          exact ⟨k, hpD, hk⟩
      rw [hInter, hkey]
      have hfst : Prod.fst '' (range (fun x : ℕ → ℕ => (g x, encSeq x))) = range g := by
        rw [← Set.range_comp]
        rfl
      rw [hfst, hgs]

end Work.Topology
