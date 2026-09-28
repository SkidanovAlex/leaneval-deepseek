import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Q44Main.parts
import Submission.Work.HP.Q44Main.conj1_basic
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.MDBasic.finite_sets

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open Classical
namespace Work.HP.Q44Main
open Work.HP

/-- The family of candidate lattices through the pairs of `Q44Pair Z Δ`. -/
def Ufam (Z Δ : ℝ) : Finset (Submodule ℤ (Fin 5 → ℤ)) :=
  ((Q44Pair_finite Z Δ).toFinset).image (q44Lat Z Δ)

lemma Ufam_spec {Z Δ : ℝ} {L : Submodule ℤ (Fin 5 → ℤ)} (hL : L ∈ Ufam Z Δ) :
    IsPrimLat L ∧ rk L = 3 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ Z ∧ lam L 2 ≤ Z := by
  classical
  rw [Ufam] at hL
  rw [Finset.mem_image] at hL
  obtain ⟨p, hp, hpeq⟩ := hL
  have hpq : p ∈ Q44Pair Z Δ := by rwa [Set.Finite.mem_toFinset] at hp
  obtain ⟨hprim, hrk, h1, h2, hdet⟩ := q44Lat_spec hpq
  have hne : p.1 ≠ 0 := by
    intro h
    have hLI := hpq.1
    rw [h] at hLI
    rw [LinearIndependent.pair_iff] at hLI
    exact one_ne_zero (hLI 1 0 (by simp)).1
  subst hpeq
  refine ⟨hprim, hrk, hdet, ?_, ?_⟩
  · exact le_trans ((lam_basic (Fin 5) (q44Lat Z Δ p)).2.2.2.1 p.1 h1 hne) hpq.2.1
  · refine le_trans ((lam_basic (Fin 5) (q44Lat Z Δ p)).2.2.2.2 p.1 p.2 h1 h2 hpq.1) ?_
    exact max_le hpq.2.1 hpq.2.2.1

lemma pairSetS_finite (L : Submodule ℤ (Fin 5 → ℤ)) (Z : ℝ) : (pairSetS L Z).Finite :=
  ((MDBasic.finite_eNorm_le (ι := Fin 5) Z).prod
    (MDBasic.finite_eNorm_le (ι := Fin 5) Z)).subset
    (fun p hp => ⟨hp.2.2.1, hp.2.2.2.1⟩)

lemma pairSetT_finite (L : Submodule ℤ (Fin 5 → ℤ)) (c : Mon 4 4 → ℤ) (Z : ℝ) :
    (pairSetT L c Z).Finite :=
  ((MDBasic.finite_eNorm_le (ι := Fin 5) Z).prod
    (MDBasic.finite_eNorm_le (ι := Fin 5) Z)).subset
    (fun p hp => ⟨hp.2.2.1, hp.2.2.2.1⟩)

/-- Per-witness bound: the number of pairs of `Q44Pair Z Δ` on which `c` vanishes is controlled
by the sum over the candidate lattices of the (T- or S-)per-lattice count for `c`. -/
lemma Nc_le (Z Δ : ℝ) (c : Mon 4 4 → ℤ) :
    (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ)
      ≤ ∑ L ∈ Ufam Z Δ,
          (if c ∈ vanishOn L then ((pairSetS L Z).ncard : ℝ) else ((pairSetT L c Z).ncard : ℝ)) := by
  classical
  have hNfin : ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
      p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).Finite :=
    (Q44Pair_finite Z Δ).subset (fun p hp => hp.1)
  have hcard : (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
        p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ)
      = ∑ L ∈ (hNfin.toFinset).image (q44Lat Z Δ),
          (((hNfin.toFinset).filter (fun p => q44Lat Z Δ p = L)).card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hNfin]
    rw [Finset.card_eq_sum_card_fiberwise (f := q44Lat Z Δ) (s := hNfin.toFinset)
      (t := (hNfin.toFinset).image (q44Lat Z Δ))
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
    push_cast
    rfl
  have himg : (hNfin.toFinset).image (q44Lat Z Δ) ⊆ Ufam Z Δ := by
    intro L hL
    rw [Finset.mem_image] at hL
    obtain ⟨p, hp, rfl⟩ := hL
    have hpN : p ∈ ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
        p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _) := by
      rwa [Set.Finite.mem_toFinset] at hp
    rw [Ufam, Finset.mem_image]
    refine ⟨p, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact hpN.1
  have hper : ∀ L ∈ (hNfin.toFinset).image (q44Lat Z Δ),
      (((hNfin.toFinset).filter (fun p => q44Lat Z Δ p = L)).card : ℝ) ≤
        (if c ∈ vanishOn L then ((pairSetS L Z).ncard : ℝ) else ((pairSetT L c Z).ncard : ℝ)) := by
    intro L _
    by_cases hcv : c ∈ vanishOn L
    · rw [if_pos hcv]
      have hsub : ((hNfin.toFinset).filter (fun p => q44Lat Z Δ p = L)) ⊆
          (pairSetS_finite L Z).toFinset := by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpN, hpg⟩ := hp
        have hpN' : p ∈ ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _) := by
          rwa [Set.Finite.mem_toFinset] at hpN
        have hpQ : p ∈ Q44Pair Z Δ := hpN'.1
        obtain ⟨-, -, h1, h2, -⟩ := q44Lat_spec hpQ
        rw [Set.Finite.mem_toFinset]
        refine ⟨?_, ?_, hpQ.2.1, hpQ.2.2.1, hpQ.1⟩
        · rw [← hpg]; exact h1
        · rw [← hpg]; exact h2
      have := Finset.card_le_card hsub
      rw [Set.ncard_eq_toFinset_card _ (pairSetS_finite L Z)]
      exact_mod_cast this
    · rw [if_neg hcv]
      have hsub : ((hNfin.toFinset).filter (fun p => q44Lat Z Δ p = L)) ⊆
          (pairSetT_finite L c Z).toFinset := by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpN, hpg⟩ := hp
        have hpN' : p ∈ ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _) := by
          rwa [Set.Finite.mem_toFinset] at hpN
        have hpQ : p ∈ Q44Pair Z Δ := hpN'.1
        have hgam := (MDBasic.mem_Gam_iff 4 4 p.1 p.2 c).mp hpN'.2
        obtain ⟨-, -, h1, h2, -⟩ := q44Lat_spec hpQ
        rw [Set.Finite.mem_toFinset]
        refine ⟨?_, ?_, hpQ.2.1, hpQ.2.2.1, hpQ.1, hgam.1, hgam.2⟩
        · rw [← hpg]; exact h1
        · rw [← hpg]; exact h2
      have := Finset.card_le_card hsub
      rw [Set.ncard_eq_toFinset_card _ (pairSetT_finite L c Z)]
      exact_mod_cast this
  calc (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
          p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ)
      = ∑ L ∈ (hNfin.toFinset).image (q44Lat Z Δ),
          (((hNfin.toFinset).filter (fun p => q44Lat Z Δ p = L)).card : ℝ) := hcard
    _ ≤ ∑ L ∈ (hNfin.toFinset).image (q44Lat Z Δ),
          (if c ∈ vanishOn L then ((pairSetS L Z).ncard : ℝ) else ((pairSetT L c Z).ncard : ℝ)) :=
        Finset.sum_le_sum hper
    _ ≤ ∑ L ∈ Ufam Z Δ,
          (if c ∈ vanishOn L then ((pairSetS L Z).ncard : ℝ) else ((pairSetT L c Z).ncard : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun L _ _ => by
          by_cases h : c ∈ vanishOn L
          · rw [if_pos h]; exact Nat.cast_nonneg _
          · rw [if_neg h]; exact Nat.cast_nonneg _)

/-- Split form of `Nc_le`. -/
lemma Nc_le' (Z Δ : ℝ) (c : Mon 4 4 → ℤ) :
    (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ)
      ≤ (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ))
        + (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∉ vanishOn L), ((pairSetT L c Z).ncard : ℝ)) := by
  classical
  refine le_trans (Nc_le Z Δ c) (le_of_eq ?_)
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun L _ => ?_)
  by_cases h : c ∈ vanishOn L <;> simp [h]

end Work.HP.Q44Main
