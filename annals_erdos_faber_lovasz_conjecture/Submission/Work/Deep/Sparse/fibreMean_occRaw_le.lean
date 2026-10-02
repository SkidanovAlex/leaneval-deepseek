import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.SliceDefs

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open scoped BigOperators
open scoped Classical

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Auxiliary notions for the occupancy bound

`occRaw A h j` counts the colours occurring at least `j` times on `A`.  Averaged over the
uniform random colouring `g` of the coordinates in `A` (the fibre through `f`), this number is
at most `k * ((A.card / k)^j / j!)`: the standard first-moment bound obtained by writing the
occupancy count as a sum of colour-wise indicators and bounding each of them with a union bound
over `j`-subsets of `A`. -/

/-- `good A c g S` says that the colouring `g` takes the value `c` everywhere on `S`. -/
private def good {k : ℕ} (A : Finset V) (c : Fin k) (g : ↥A → Fin k) (S : Finset ↥A) : Prop :=
  ∀ a ∈ S, g a = c

/-- The number of coordinates of `A` on which `g` takes the value `c`. -/
private def cntG {k : ℕ} (A : Finset V) (c : Fin k) (g : ↥A → Fin k) : ℕ :=
  ((Finset.univ : Finset ↥A).filter (fun a => g a = c)).card

/-- The indicator of the event `good A c g S`, as a real number. -/
private noncomputable def indGood {k : ℕ} (A : Finset V) (c : Fin k) (g : ↥A → Fin k)
    (S : Finset ↥A) : ℝ :=
  if good A c g S then (1 : ℝ) else 0

/-- The indicator of the event that `c` occurs at least `j` times on `A` under `g`. -/
private noncomputable def indOcc {k : ℕ} (A : Finset V) (c : Fin k) (g : ↥A → Fin k)
    (j : ℕ) : ℝ :=
  if j ≤ cntG A c g then (1 : ℝ) else 0

/-- `occRaw` as a sum over colours of the indicators of the events "`c` occurs at least `j`
times on `A`". -/
private theorem occRaw_eq_sum {k : ℕ} (A : Finset V) (h : V → Fin k) (j : ℕ) :
    (occRaw A h j : ℝ)
      = ∑ c : Fin k, (if j ≤ (A.filter (fun x => h x = c)).card then (1:ℝ) else 0) := by
  rw [Finset.sum_boole (R := ℝ)
    (p := fun c => j ≤ (A.filter (fun x => h x = c)).card) (s := Finset.univ)]
  unfold occRaw
  rfl

/-- The `A`-filter counting the occurrences of a colour only depends on the values of the
colouring on `A`. -/
private theorem graft_filter {k : ℕ} (A : Finset V) (g : ↥A → Fin k) (f : V → Fin k)
    (c : Fin k) :
    A.filter (fun x => graft A g f x = c)
      = ((Finset.univ : Finset ↥A).filter (fun a => g a = c)).image Subtype.val := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hxA, hx⟩
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    rwa [graft_apply_of_mem] at hx
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, by rwa [graft_apply_of_mem]⟩

private theorem graft_cnt {k : ℕ} (A : Finset V) (g : ↥A → Fin k) (f : V → Fin k) (c : Fin k) :
    (A.filter (fun x => graft A g f x = c)).card = cntG A c g := by
  rw [graft_filter A g f c, Finset.card_image_of_injective _ Subtype.val_injective]
  rfl

/-- `occRaw` of a grafted colouring, expressed through the colouring of the fibre. -/
private theorem occRaw_graft_eq_sum {k : ℕ} (A : Finset V) (f : V → Fin k) (g : ↥A → Fin k)
    (j : ℕ) :
    (occRaw A (graft A g f) j : ℝ) = ∑ c : Fin k, indOcc A c g j := by
  rw [occRaw_eq_sum A (graft A g f) j]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [graft_cnt A g f c]
  rfl

/-! ## Probabilistic ingredients -/

/-- The fibrewise mean of the indicator of `good A c · S` is the probability of that event
under the uniform colouring of the fibre. -/
private theorem fibre_prob {k : ℕ} (A : Finset V) [Nonempty (↥A → Fin k)]
    (c : Fin k) (S : Finset ↥A) :
    (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, indGood A c g S
      = (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | good A c g S} := by
  classical
  have hcard : Fintype.card (↥A → Fin k) = k ^ A.card := by
    rw [card_colSpace, Fintype.card_coe]
  rw [FinSpace.prob, colSpace_mass, hcard, Nat.cast_pow]
  have h1 : ∀ g : ↥A → Fin k,
      {g : ↥A → Fin k | good A c g S}.indicator (fun _ => ((k:ℝ) ^ A.card)⁻¹) g
      = ((k:ℝ) ^ A.card)⁻¹ * indGood A c g S := by
    intro g
    by_cases h : good A c g S
    · rw [Set.indicator_of_mem (show g ∈ {g : ↥A → Fin k | good A c g S} from h)]
      unfold indGood
      rw [if_pos h, mul_one]
    · rw [Set.indicator_of_notMem (show g ∉ {g : ↥A → Fin k | good A c g S} from h)]
      unfold indGood
      rw [if_neg h, mul_zero]
  rw [Finset.sum_congr rfl (fun g _ => h1 g), one_div]
  exact Finset.mul_sum Finset.univ (fun g => indGood A c g S) (((k:ℝ) ^ A.card)⁻¹)

/-- **Product law for pinned values.**  Under the uniform colouring of the fibre `↥A → Fin k`,
the event that the colour `c` is used on every element of `S` has probability `(1/k)^{|S|}`. -/
private theorem prob_pinned {k : ℕ} (A : Finset V) [Nonempty (↥A → Fin k)] (hk : 0 < k)
    (c : Fin k) (S : Finset ↥A) :
    (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | good A c g S} = (1 / (k:ℝ)) ^ S.card := by
  classical
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hset : {g : ↥A → Fin k | good A c g S}
      = ↑(Fintype.piFinset (fun a : ↥A =>
          if a ∈ S then ({c} : Finset (Fin k)) else Finset.univ)) := by
    ext g
    simp only [Set.mem_ofPred_eq, good, Finset.mem_coe, Fintype.mem_piFinset]
    constructor
    · intro hg a
      by_cases h : a ∈ S
      · rw [if_pos h, Finset.mem_singleton]; exact hg a h
      · rw [if_neg h]; exact Finset.mem_univ _
    · intro hg a ha
      have := hg a
      rwa [if_pos ha, Finset.mem_singleton] at this
  rw [hset, colSpace_prob_pi]
  have hprod : (∏ a : ↥A,
        (((if a ∈ S then ({c} : Finset (Fin k)) else Finset.univ).card : ℝ) / (k:ℝ)))
      = ∏ a : ↥A, (if a ∈ S then (1 / (k:ℝ)) else 1) := by
    refine Finset.prod_congr rfl fun a _ => ?_
    by_cases h : a ∈ S
    · rw [if_pos h, if_pos h, Finset.card_singleton, Nat.cast_one, one_div]
    · rw [if_neg h, if_neg h, Finset.card_univ, Fintype.card_fin]
      exact div_self hk0
  rw [hprod]
  have step1 : ∏ a : ↥A, (if a ∈ S then (1/(k:ℝ)) else 1)
      = ∏ a ∈ S, (if a ∈ S then (1/(k:ℝ)) else 1) :=
    (Finset.prod_subset (Finset.subset_univ S) (fun a _ ha => by rw [if_neg ha])).symm
  have step2 : ∏ a ∈ S, (if a ∈ S then (1/(k:ℝ)) else 1) = ∏ a ∈ S, (1/(k:ℝ)) :=
    Finset.prod_congr rfl (fun a ha => by rw [if_pos ha])
  rw [step1, step2, Finset.prod_const]

/-! ## The colour-wise bound -/

/-- **The colour-wise union bound.**  Averaged over the fibre, the indicator that a fixed colour
`c` occurs at least `j` times is at most `C(|A|, j) / k^j`. -/
private theorem fibre_col_le {k : ℕ} (A : Finset V) [Nonempty (↥A → Fin k)] (hk : 0 < k)
    {j : ℕ} (c : Fin k) :
    (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, indOcc A c g j
      ≤ (A.card.choose j : ℝ) * (1 / (k:ℝ)) ^ j := by
  classical
  have hkn : (0:ℝ) < (k:ℝ) ^ A.card := pow_pos (by exact_mod_cast hk) _
  have hne : (0:ℝ) ≤ 1 / (k:ℝ) ^ A.card := le_of_lt (one_div_pos.2 hkn)
  set pc : Finset (Finset ↥A) := Finset.powersetCard j (Finset.univ : Finset ↥A) with hpc
  have hpt : ∀ g : ↥A → Fin k, indOcc A c g j ≤ ∑ S ∈ pc, indGood A c g S := by
    intro g
    by_cases hjc : j ≤ cntG A c g
    · have hpos : 0 < (Finset.powersetCard j
          ((Finset.univ : Finset ↥A).filter (fun a => g a = c))).card := by
        rw [Finset.card_powersetCard]
        exact Nat.choose_pos hjc
      obtain ⟨S, hSmem⟩ := Finset.card_pos.1 hpos
      rw [Finset.mem_powersetCard] at hSmem
      obtain ⟨hSsub, hScard⟩ := hSmem
      have hSpc : S ∈ pc := by
        rw [hpc, Finset.mem_powersetCard]
        exact ⟨hSsub.trans (Finset.filter_subset _ _), hScard⟩
      have hSval : indGood A c g S = 1 := by
        rw [indGood]
        rw [if_pos]
        exact fun a ha => (Finset.mem_filter.1 (hSsub ha)).2
      calc indOcc A c g j = 1 := by rw [indOcc]; rw [if_pos hjc]
        _ = indGood A c g S := hSval.symm
        _ ≤ ∑ S' ∈ pc, indGood A c g S' :=
            Finset.single_le_sum (f := fun S' => indGood A c g S')
              (fun S' _ => by by_cases h : good A c g S' <;> simp [indGood, h]) hSpc
    · rw [indOcc]
      rw [if_neg hjc]
      exact Finset.sum_nonneg (fun S' _ => by by_cases h : good A c g S' <;> simp [indGood, h])
  have hstep : (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, indOcc A c g j
      ≤ (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, ∑ S ∈ pc, indGood A c g S :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun g _ => hpt g)) hne
  have hB : ∑ g : ↥A → Fin k, (1 / (k:ℝ) ^ A.card) * (∑ S ∈ pc, indGood A c g S)
      = ∑ g : ↥A → Fin k, ∑ S ∈ pc, (1 / (k:ℝ) ^ A.card) * indGood A c g S :=
    Finset.sum_congr rfl (fun g _ =>
      Finset.mul_sum pc (fun S => indGood A c g S) (1 / (k:ℝ) ^ A.card))
  have hswap : (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, ∑ S ∈ pc, indGood A c g S
      = ∑ S ∈ pc, (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, indGood A c g S := by
    rw [Finset.mul_sum]
    rw [hB, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun S _ =>
      (Finset.mul_sum Finset.univ (fun g => indGood A c g S) (1 / (k:ℝ) ^ A.card)).symm)
  have hprob : ∑ S ∈ pc, (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, indGood A c g S
      = ∑ S ∈ pc, (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | good A c g S} := by
    exact Finset.sum_congr rfl (fun S _ => fibre_prob A c S)
  have hpinned : ∑ S ∈ pc, (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | good A c g S}
      = ∑ S ∈ pc, (1 / (k:ℝ)) ^ S.card :=
    Finset.sum_congr rfl (fun S _ => prob_pinned A hk c S)
  have hcards : ∑ S ∈ pc, (1 / (k:ℝ)) ^ S.card = ∑ S ∈ pc, (1 / (k:ℝ)) ^ j :=
    Finset.sum_congr rfl (fun S hS => by rw [(Finset.mem_powersetCard.1 hS).2])
  have hpc_card : ∑ S ∈ pc, (1 / (k:ℝ)) ^ j = (A.card.choose j : ℝ) * (1 / (k:ℝ)) ^ j := by
    rw [Finset.sum_const, hpc, Finset.card_powersetCard, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul]
  calc (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, indOcc A c g j
      ≤ (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, ∑ S ∈ pc, indGood A c g S := hstep
    _ = ∑ S ∈ pc, (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, indGood A c g S := hswap
    _ = ∑ S ∈ pc, (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | good A c g S} := hprob
    _ = ∑ S ∈ pc, (1 / (k:ℝ)) ^ S.card := hpinned
    _ = ∑ S ∈ pc, (1 / (k:ℝ)) ^ j := hcards
    _ = (A.card.choose j : ℝ) * (1 / (k:ℝ)) ^ j := hpc_card

/-! ## The main estimate -/

theorem fibreMean_occRaw_le {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (A : Finset V) {j : ℕ} (hj : 0 < j) (f : V → Fin k) :
    fibreMean A (fun f' : V → Fin k => (occRaw A f' j : ℝ)) f
      ≤ (k : ℝ) * (((A.card : ℝ) / (k : ℝ)) ^ j / (j.factorial : ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hzero : ∀ f' : V → Fin 0, occRaw A f' j = 0 := by
      intro f'
      unfold occRaw
      have hempty : (Finset.univ : Finset (Fin 0)) = ∅ := by
        ext c
        exact absurd c.isLt (by omega)
      rw [hempty]
      simp
    have hL : fibreMean A (fun f' : V → Fin 0 => (occRaw A f' j : ℝ)) f = 0 := by
      have hfun : (fun f' : V → Fin 0 => (occRaw A f' j : ℝ)) = fun _ => 0 := by
        funext f'
        rw [hzero f']
        norm_num
      rw [hfun, fibreMean]
      simp
    rw [hL]
    simp
  · haveI : Nonempty (↥A → Fin k) := ⟨fun _ => ⟨0, hkpos⟩⟩
    have hstep1 : fibreMean A (fun f' : V → Fin k => (occRaw A f' j : ℝ)) f
        = (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, ∑ c : Fin k, indOcc A c g j := by
      rw [fibreMean]
      congr 1
      exact Finset.sum_congr rfl (fun g _ => occRaw_graft_eq_sum A f g j)
    have hstep2 : (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, ∑ c : Fin k, indOcc A c g j
        = ∑ c : Fin k, (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, indOcc A c g j := by
      rw [Finset.mul_sum]
      have hB : ∑ g : ↥A → Fin k, (1 / (k:ℝ) ^ A.card) * (∑ c : Fin k, indOcc A c g j)
          = ∑ g : ↥A → Fin k, ∑ c : Fin k, (1 / (k:ℝ) ^ A.card) * indOcc A c g j :=
        Finset.sum_congr rfl (fun g _ =>
          Finset.mul_sum Finset.univ (fun c => indOcc A c g j) (1 / (k:ℝ) ^ A.card))
      rw [hB, Finset.sum_comm]
      exact Finset.sum_congr rfl (fun c _ =>
        (Finset.mul_sum Finset.univ (fun g => indOcc A c g j) (1 / (k:ℝ) ^ A.card)).symm)
    have hstep3 : ∑ c : Fin k, (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, indOcc A c g j
        ≤ ∑ c : Fin k, (A.card.choose j : ℝ) * (1 / (k:ℝ)) ^ j :=
      Finset.sum_le_sum (fun c _ => fibre_col_le A hkpos c)
    have hstep4 : ∑ c : Fin k, (A.card.choose j : ℝ) * (1 / (k:ℝ)) ^ j
        = (k : ℝ) * ((A.card.choose j : ℝ) * (1 / (k:ℝ)) ^ j) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hstep5 : (k : ℝ) * ((A.card.choose j : ℝ) * (1 / (k:ℝ)) ^ j)
        ≤ (k : ℝ) * (((A.card : ℝ) / (k : ℝ)) ^ j / (j.factorial : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : (A.card.choose j : ℝ) ≤ (A.card:ℝ) ^ j / (j.factorial:ℝ) :=
        Nat.choose_le_pow_div j A.card
      have h2 : (0:ℝ) ≤ (1 / (k:ℝ)) ^ j :=
        pow_nonneg (one_div_nonneg.2 (Nat.cast_nonneg k)) j
      have h3 : (A.card.choose j : ℝ) * (1 / (k:ℝ)) ^ j
          ≤ ((A.card:ℝ) ^ j / (j.factorial:ℝ)) * (1 / (k:ℝ)) ^ j :=
        mul_le_mul_of_nonneg_right h1 h2
      have h4 : ((A.card:ℝ) ^ j / (j.factorial:ℝ)) * (1 / (k:ℝ)) ^ j
          = ((A.card : ℝ) / (k : ℝ)) ^ j / (j.factorial : ℝ) := by
        rw [one_div_pow, div_pow]
        ring
      rw [h4] at h3
      exact h3
    calc fibreMean A (fun f' : V → Fin k => (occRaw A f' j : ℝ)) f
        = (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, ∑ c : Fin k, indOcc A c g j := hstep1
      _ = ∑ c : Fin k, (1 / (k:ℝ) ^ A.card) * ∑ g : ↥A → Fin k, indOcc A c g j := hstep2
      _ ≤ ∑ c : Fin k, (A.card.choose j : ℝ) * (1 / (k:ℝ)) ^ j := hstep3
      _ = (k : ℝ) * ((A.card.choose j : ℝ) * (1 / (k:ℝ)) ^ j) := hstep4
      _ ≤ (k : ℝ) * (((A.card : ℝ) / (k : ℝ)) ^ j / (j.factorial : ℝ)) := hstep5

end Work.Deep.Sparse
