import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Q44Main.parts
import Submission.Work.HP.dmin_le_exists_prim
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Q44Child.gam_rank
import Submission.Work.HP.Q44Child.lam_attained

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace Work.HP.Q44Main
open Work.HP

/-! ## Infrastructure -/

/-- The set of candidate witness forms: nonzero coefficient vectors of norm at most `M`. -/
def witSet (M : ℝ) : Set (Mon 4 4 → ℤ) := {c | c ≠ 0 ∧ eNorm c ≤ M}

lemma witSet_finite (M : ℝ) : (witSet M).Finite :=
  (MDBasic.finite_eNorm_le (ι := Mon 4 4) M).subset (fun c hc => hc.2)

/-- If `λ₁(Γ_{x,y}) ≤ M` there is a nonzero witness `c ∈ Γ_{x,y}` of norm at most `M`. -/
theorem exists_witness {x y : Fin 5 → ℤ} {M : ℝ} (h : lam (Gam 4 4 x y) 1 ≤ M) :
    ∃ c : Mon 4 4 → ℤ, c ∈ Gam 4 4 x y ∧ c ≠ 0 ∧ eNorm c ≤ M := by
  have h1 : (1 : ℕ) ≤ rk (Gam 4 4 x y) := le_trans (by norm_num) (Q44Child.gam_rank x y)
  obtain ⟨f, hfL, hfI, hfb⟩ := Q44Child.lamAttained_aux (Gam 4 4 x y) h1
  exact ⟨f 0, hfL 0, hfI.ne_zero 0, le_trans (hfb 0) h⟩

/-- The pair set `Q44Pair Z Δ` is finite. -/
lemma Q44Pair_finite (Z Δ : ℝ) : (Q44Pair Z Δ).Finite :=
  Set.Finite.subset
    ((MDBasic.finite_eNorm_le (ι := Fin 5) Z).prod (MDBasic.finite_eNorm_le (ι := Fin 5) Z))
    (fun p hp => ⟨hp.2.1, hp.2.2.1⟩)

/-- `ℓ^{(1)} ≤ #(Q44Pair)`. -/
theorem ell44_one_le_Q44Pair (Z Δ M : ℝ) : ell44 1 Z Δ M ≤ (Q44Pair Z Δ).ncard := by
  rw [ell44_eq]
  exact Set.ncard_le_ncard (Q44PairLam_subset 1 Z Δ M) (Q44Pair_finite Z Δ)

/-- A canonical rank-`3` primitive lattice through a counted pair. -/
def q44Lat (Z Δ : ℝ) (p : (Fin 5 → ℤ) × (Fin 5 → ℤ)) : Submodule ℤ (Fin 5 → ℤ) := by
  classical
  exact if h : p ∈ Q44Pair Z Δ then
    Classical.choose
      (dmin_le_exists_prim (Fin 5) 3 p.1 p.2 Δ h.1 (by norm_num) (by simp) h.2.2.2)
  else ⊥

lemma q44Lat_spec {Z Δ : ℝ} {p} (hp : p ∈ Q44Pair Z Δ) :
    IsPrimLat (q44Lat Z Δ p) ∧ rk (q44Lat Z Δ p) = 3 ∧ p.1 ∈ q44Lat Z Δ p ∧
      p.2 ∈ q44Lat Z Δ p ∧ detL (q44Lat Z Δ p) ≤ Δ + 1 := by
  rw [q44Lat, dif_pos hp]
  exact Classical.choose_spec
    (dmin_le_exists_prim (Fin 5) 3 p.1 p.2 Δ hp.1 (by norm_num) (by simp) hp.2.2.2)

/-- A canonical witness form for each counted pair. -/
def witF (Z Δ M : ℝ) (p : (Fin 5 → ℤ) × (Fin 5 → ℤ)) : (Mon 4 4 → ℤ) := by
  classical
  exact if h : p ∈ Q44PairLam 1 Z Δ M then
    Classical.choose (exists_witness (x := p.1) (y := p.2) h.2.2.2.2)
  else 0

lemma witF_spec {Z Δ M : ℝ} {p} (hp : p ∈ Q44PairLam 1 Z Δ M) :
    witF Z Δ M p ∈ Gam 4 4 p.1 p.2 ∧ witF Z Δ M p ≠ 0 ∧ eNorm (witF Z Δ M p) ≤ M := by
  rw [witF, dif_pos hp]
  exact Classical.choose_spec (exists_witness (x := p.1) (y := p.2) hp.2.2.2.2)

/-- **Witness decomposition.** `ℓ^{(1)}` is at most the sum, over the candidate witnesses `c`,
of the number of pairs of `Q44Pair` on which `c` vanishes. -/
theorem ell44_one_le_witsum (Z Δ M : ℝ) (hZ : 1 ≤ Z) :
    (ell44 1 Z Δ M : ℝ) ≤
      ∑ c ∈ (witSet_finite M).toFinset,
        (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ) := by
  classical
  set S : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) := Q44PairLam 1 Z Δ M with hSdef
  have hSfin : S.Finite := (Q44Pair_finite Z Δ).subset (Q44PairLam_subset 1 Z Δ M)
  set g : (Fin 5 → ℤ) × (Fin 5 → ℤ) → (Mon 4 4 → ℤ) := witF Z Δ M with hgdef
  -- the image is contained in the witness set
  have himg : ∀ c ∈ (hSfin.toFinset).image g, c ∈ (witSet_finite M).toFinset := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    have hpS : p ∈ S := by rwa [Set.Finite.mem_toFinset] at hp
    rw [Set.Finite.mem_toFinset]
    exact ⟨(witF_spec (by rwa [hSdef] at hpS)).2.1, (witF_spec (by rwa [hSdef] at hpS)).2.2⟩
  -- fiber decomposition
  have hcard : (S.ncard : ℝ) = ∑ c ∈ (hSfin.toFinset).image g,
      (((hSfin.toFinset).filter (fun p => g p = c)).card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hSfin]
    rw [Finset.card_eq_sum_card_fiberwise (f := g) (s := hSfin.toFinset)
      (t := (hSfin.toFinset).image g) (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
    push_cast
    rfl
  -- each fiber is controlled by the set on which `c` vanishes
  have hfib : ∀ c ∈ (hSfin.toFinset).image g,
      (((hSfin.toFinset).filter (fun p => g p = c)).card : ℝ)
        ≤ (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ) := by
    intro c hc
    have hNfin : ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
        p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).Finite :=
      (Q44Pair_finite Z Δ).subset (fun p hp => hp.1)
    have hsub : ((hSfin.toFinset).filter (fun p => g p = c)) ⊆
        (hNfin.toFinset) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hpg⟩ := hp
      have hpS' : p ∈ S := by rwa [Set.Finite.mem_toFinset] at hpS
      have hpQ : p ∈ Q44Pair Z Δ := (Q44PairLam_subset 1 Z Δ M) (by rwa [hSdef] at hpS')
      have hgam : c ∈ Gam 4 4 p.1 p.2 := by
        rw [← hpg]; exact (witF_spec (by rwa [hSdef] at hpS')).1
      rw [Set.Finite.mem_toFinset]
      exact ⟨hpQ, hgam⟩
    have := Finset.card_le_card hsub
    rw [Set.ncard_eq_toFinset_card _ hNfin]
    exact_mod_cast this
  calc (ell44 1 Z Δ M : ℝ) = (S.ncard : ℝ) := by rw [ell44_eq, hSdef]
    _ = ∑ c ∈ (hSfin.toFinset).image g, (((hSfin.toFinset).filter (fun p => g p = c)).card : ℝ) := hcard
    _ ≤ ∑ c ∈ (hSfin.toFinset).image g,
          (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ) := Finset.sum_le_sum hfib
    _ ≤ ∑ c ∈ (witSet_finite M).toFinset,
          (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun c _ _ => Nat.cast_nonneg _)

end Work.HP.Q44Main
