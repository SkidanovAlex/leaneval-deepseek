import Mathlib
import Submission.Szemeredi.Removal.CountLemmaFast
import Submission.Szemeredi.Removal.GoodAtomsMain

/-!
# The hypergraph removal lemma (`main-2`) for the complete hypergraph

Tao, *A variant of the hypergraph removal lemma* (arXiv:math/0503572), Theorem `main-2`,
specialised to the complete `d`-uniform hypergraph on `Fin (d+1)` (all parts `V i`).

Given `E_e ∈ A_e` with `avg (∏_{e ∈ H_d} 1_{E_e}) ≤ δ`, there are `E'_e ⊆ E_e` with
`⋂_{e ∈ H_d} E'_e = ∅` and `avg (1_{E_e \ E'_e}) ≤ ε` (with `δ` depending only on
`d` and `ε`).
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-- The complete `d`-uniform hypergraph on `Fin (d+1)`. -/
noncomputable def HdC (d : ℕ) : Finset (Finset (Fin (d+1))) :=
  Finset.univ.filter (fun e => e.card = d)

theorem mem_HdC {d : ℕ} {e : Finset (Fin (d+1))} : e ∈ HdC d ↔ e.card = d := by
  simp [HdC]

theorem univ_card_eq (d : ℕ) : (Finset.univ : Finset (Fin (d+1))).card = d + 1 := by simp

theorem HdC_nonempty (d : ℕ) : ∃ e ∈ HdC d, True := by
  obtain ⟨u, -, -, hcard⟩ :=
    Finset.exists_subsuperset_card_eq (s := (∅ : Finset (Fin (d+1)))) (t := Finset.univ)
      (by simp) (Nat.zero_le d) (by rw [univ_card_eq]; omega)
  exact ⟨u, mem_HdC.mpr hcard, trivial⟩

/-- The down-closure of the complete hypergraph is everything of size `≤ d`. -/
theorem hall_HdC {d : ℕ} {f : Finset (Fin (d+1))} (hf : f.card ≤ d) : f ∈ Hall (HdC d) := by
  obtain ⟨u, hfu, -, hcard⟩ :=
    Finset.exists_subsuperset_card_eq (s := f) (t := Finset.univ) (by simp) hf
      (by rw [univ_card_eq]; omega)
  exact mem_Hall.mpr ⟨u, mem_HdC.mpr hcard, hfu⟩

theorem hall_HdC_iff {d : ℕ} {f : Finset (Fin (d+1))} : f ∈ Hall (HdC d) ↔ f.card ≤ d := by
  refine ⟨fun hf => ?_, hall_HdC⟩
  obtain ⟨e, he, hfe⟩ := mem_Hall.mp hf
  have := mem_HdC.mp he
  calc f.card ≤ e.card := Finset.card_le_card hfe
    _ = d := this

theorem mem_lev_HdC {d j : ℕ} (hj : j ≤ d) {f : Finset (Fin (d+1))} :
    f ∈ lev (HdC d) (d - j) ↔ f.card = j := by
  constructor
  · intro hf
    obtain ⟨e, he, -, hcard⟩ := mem_lev_iff.mp hf
    rw [mem_HdC.mp he] at hcard
    omega
  · intro hf
    rw [mem_lev_iff]
    obtain ⟨u, hfu, -, hcard⟩ :=
      Finset.exists_subsuperset_card_eq (n := d) (s := f) (t := Finset.univ) (by simp)
        (by omega) (by rw [univ_card_eq]; omega)
    refine ⟨u, mem_HdC.mpr hcard, hfu, ?_⟩
    rw [hf, hcard]
    omega

/-! ## Measurability of the bad sets -/

section Meas

variable {β γ Ω : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
  [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- The set of points where the largeness condition on a boundary atom tuple fails
is measurable for the join of the boundary σ-algebras. -/
theorem isMeas_lBadSet (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω) (P : β → SigAlg Ω) :
    (SigAlg.iInf P Finset.univ).IsMeas (LBadSet F M j Ae P) := by
  intro x hx y hy
  rw [mem_lBadSet] at hx ⊢
  have hblock : ∀ i : β, (P i).block y = (P i).block x := by
    intro i
    have hy' : y ∈ (P i).block x := by
      rw [iInf_block, Finset.mem_inf] at hy
      exact hy i (Finset.mem_univ i)
    exact SigAlg.block_eq_of_mem hy'
  have hfun : (fun i : β => (P i).block y) = (fun i : β => (P i).block x) := funext hblock
  rw [hfun]
  exact hx

/-- The set of points where the regularity condition on a lower-order atom tuple
fails is measurable for the join of the lower-order σ-algebras. -/
theorem isMeas_rBadSet (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω)
    (P P' : β → SigAlg Ω) (Q : γ → SigAlg Ω) :
    (SigAlg.iInf Q Finset.univ).IsMeas (RBadSet F M j Ae P P' Q) := by
  intro x hx y hy
  rw [mem_rBadSet] at hx ⊢
  have hblock : ∀ i : γ, (Q i).block y = (Q i).block x := by
    intro i
    have hy' : y ∈ (Q i).block x := by
      rw [iInf_block, Finset.mem_inf] at hy
      exact hy i (Finset.mem_univ i)
    exact SigAlg.block_eq_of_mem hy'
  have hfun : (fun i : γ => (Q i).block y) = (fun i : γ => (Q i).block x) := funext hblock
  rw [hfun]
  exact hx

end Meas

/-! ## Coordinate measurability -/

theorem coord_empty_eq_triv : coord (V := V) (∅ : Finset ι) = (SigAlg.triv : SigAlg (Pt V)) := by
  refine SigAlg.ext (fun x => ?_)
  rw [coord_block, triv_block]
  simp

/-- Every `coord f`-measurable set is `coord g`-measurable for `f ⊆ g`. -/
theorem coord_isMeas_of_subset {f g : Finset ι} (hfg : f ⊆ g) {S : Finset (Pt V)}
    (h : (coord (V := V) f).IsMeas S) : (coord (V := V) g).IsMeas S := by
  rw [coord_isMeas_iff] at h ⊢
  exact fun x y hxy => h x y (fun i hi => hxy i (hfg hi))

/-- The join of a family of σ-algebras refining coordinate algebras on subsets of `f`
also refines `coord f`. -/
theorem iInf_refines_coord_of {κ : Type*} [Fintype κ] [DecidableEq κ] (T : Finset κ)
    (R : κ → SigAlg (Pt V)) (π : κ → Finset ι) {f : Finset ι}
    (hT : ∀ k ∈ T, π k ⊆ f) (hR : ∀ k ∈ T, (R k).Refines (coord (V := V) (π k))) :
    (SigAlg.iInf R T).Refines (coord (V := V) f) := by
  intro x y hy
  rw [coord_block, Finset.mem_filter] at hy
  rw [iInf_block, Finset.mem_inf]
  intro k hk
  have hyk : y ∈ (coord (V := V) (π k)).block x := by
    rw [coord_block, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i hi => hy.2 i (hT k hk hi)⟩
  exact hR k hk x hyk

section BadMeas

variable {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ} {F : ℕ → ℕ}
  {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ} {d : ℕ}

/-- The boundary algebras of a `d`-uniform hypergraph refine the coordinate algebras. -/
theorem bdryAlg_refines_coord_of (hHd : ∀ e ∈ Hd, e.card = d)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M) {j : ℕ} {f : Finset ι}
    (hfHall : f ∈ Hall Hd) (hfcard : f.card = j) :
    ∀ g' : {g' : Finset ι // g' ∈ del f},
      (bdryAlg (V := V) B j f g').Refines (coord (V := V) g'.val) := by
  have hjle : j ≤ d := by rw [← hfcard]; exact Hall_card_le hHd hfHall
  intro g'
  have h1 : g'.val ⊆ f := (mem_del.mp g'.2).1
  have h2 : g'.val.card + 1 = f.card := (mem_del.mp g'.2).2
  have h3 : g'.val.card < d := by rw [hfcard] at h2; omega
  have hHall : g'.val ∈ Hall Hd := Hall_down hfHall h1
  have hcard : j - 1 = g'.val.card := by omega
  show (B (j - 1) g'.val).Refines (coord (V := V) g'.val)
  rw [hcard]
  exact hR.2.2.2.1 g'.val.card h3 g'.val (Hall_mem_lev hHd hHall)

theorem lowAlg_refines_coord_of (hHd : ∀ e ∈ Hd, e.card = d)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M) {j : ℕ} {f : Finset ι}
    (hfHall : f ∈ Hall Hd) (hfcard : f.card = j) :
    ∀ g' : {g' : Finset ι // g' ⊂ f},
      (lowAlg (V := V) B f g').Refines (coord (V := V) g'.val) := by
  have hjle : j ≤ d := by rw [← hfcard]; exact Hall_card_le hHd hfHall
  intro g'
  have h1 : g'.val ⊆ f := g'.2.1
  have h3 : g'.val.card < d := by
    have := Finset.card_lt_card g'.2
    omega
  have hHall : g'.val ∈ Hall Hd := Hall_down hfHall h1
  exact hR.2.2.2.1 g'.val.card h3 g'.val (Hall_mem_lev hHd hHall)

/-- The bad set of an atom at a face `f` of a `d`-uniform hypergraph is `coord g`-measurable
for every `g ⊇ f`. -/
theorem badSetOf_isMeas_coord (hHd : ∀ e ∈ Hd, e.card = d)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M) {j : ℕ} {f : Finset ι}
    (hfHall : f ∈ Hall Hd) (hfcard : f.card = j) {g : Finset ι} (hfg : f ⊆ g)
    (Ae : Finset (Pt V)) :
    (coord (V := V) g).IsMeas (badSetOf (V := V) d Bd B B' M F j f Ae) := by
  have hL := (isMeas_lBadSet F M j Ae (bdryAlg (V := V) B j f)).of_refines
    (iInf_refines_coord_of Finset.univ (bdryAlg (V := V) B j f) (fun k => k.val)
      (fun k _ => (mem_del.mp k.2).1)
      (fun k _ => bdryAlg_refines_coord_of (V := V) hHd hR hfHall hfcard k))
  have hRr := (isMeas_rBadSet F M j Ae (bdryAlg (V := V) B j f) (bdryAlg (V := V) B' j f)
      (lowAlg (V := V) B f)).of_refines
    (iInf_refines_coord_of Finset.univ (lowAlg (V := V) B f) (fun k => k.val)
      (fun k _ => k.2.1) (fun k _ => lowAlg_refines_coord_of (V := V) hHd hR hfHall hfcard k))
  exact coord_isMeas_of_subset hfg (hL.union hRr)

end BadMeas


/-! ## Arithmetic helpers for the triple-exponential growth function -/

theorem two_mul_le_two_pow {x : ℕ} (hx : 2 ≤ x) : 2 * x ≤ 2 ^ x := by
  induction x with
  | zero => omega
  | succ n ih =>
    by_cases hn : n ≤ 2
    · interval_cases n <;> norm_num
    · push_neg at hn
      have h1 : 2 * n ≤ 2 ^ n := ih (by omega)
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
      have h3 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

theorem two_mul_add_one_le_two_pow {x : ℕ} (hx : 4 ≤ x) : 2 * x + 1 ≤ 2 ^ x := by
  induction x with
  | zero => omega
  | succ n ih =>
    by_cases hn : n ≤ 3
    · have hn3 : n = 3 := by omega
      subst hn3
      norm_num
    · push_neg at hn
      have h1 : 2 * n + 1 ≤ 2 ^ n := ih (by omega)
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
      have h3 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

theorem exists_two_pow_ge_div (η : ℝ) (hη : 0 < η) :
    ∃ T : ℕ, ∀ x : ℕ, T ≤ x → 4 / η ≤ (2 : ℝ) ^ x := by
  obtain ⟨T, hT⟩ := exists_nat_ge (4 / η)
  refine ⟨max T 4, fun x hx => ?_⟩
  have h1 : 4 / η ≤ (T : ℝ) := hT
  have h2 : (T : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans (le_max_left _ _) hx)
  have h3 : (x : ℝ) ≤ (2 : ℝ) ^ x := by
    exact_mod_cast (le_of_lt (Nat.lt_two_pow_self (n := x)))
  linarith

theorem log_Ffast_ge (x : ℕ) (hx : 4 ≤ x) : (2 : ℝ) ^ (2 * x) ≤ Real.log (Ffast x) := by
  have h1 : ((Ffast x : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ (2 ^ x)) := by
    unfold Ffast; push_cast; ring
  rw [h1, Real.log_pow]
  rw [show ((2 ^ (2 ^ x) : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ x) by push_cast; ring]
  have h2x : 2 * x + 1 ≤ 2 ^ x := two_mul_add_one_le_two_pow hx
  have h3 : (2 : ℝ) ^ (2 * x) * 2 ≤ (2 : ℝ) ^ (2 ^ x) := by
    have h4 : (2 : ℝ) ^ (2 * x) * 2 = (2 : ℝ) ^ (2 * x + 1) := by rw [pow_succ]
    rw [h4]
    exact pow_le_pow_right₀ (by norm_num) h2x
  have h5 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h7 : (0 : ℝ) < (2 : ℝ) ^ (2 ^ x) := by positivity
  have h8 : (2 : ℝ) ^ (2 ^ x) * (1 / 2) ≤ (2 : ℝ) ^ (2 ^ x) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h5 (le_of_lt h7)
  linarith

theorem Ffast_ge_two_pow_two_mul (x : ℕ) (hx : 2 ≤ x) : (2 : ℝ) ^ (2 * x) ≤ (Ffast x : ℝ) := by
  have h1 : ((Ffast x : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ (2 ^ x)) := by
    unfold Ffast; push_cast; ring
  rw [h1]
  refine pow_le_pow_right₀ (by norm_num) ?_
  exact le_trans (two_mul_le_two_pow hx)
    (Nat.pow_le_pow_right (by norm_num) (le_of_lt (Nat.lt_two_pow_self (n := x))))

theorem eventually_two_pow_mul_le (η : ℝ) (hη : 0 < η) :
    ∃ T : ℕ, ∀ x : ℕ, T ≤ x →
      (2 : ℝ) ^ x * (1 / Real.log (Ffast x) + 1 / (Ffast x : ℝ)) ≤ η := by
  obtain ⟨T, hT⟩ := exists_two_pow_ge_div η hη
  refine ⟨max T 4, fun x hx => ?_⟩
  have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
  have h2x : (4 : ℝ) / η ≤ (2 : ℝ) ^ x := hT x (le_trans (le_max_left _ _) hx)
  have hlog := log_Ffast_ge x hx4
  have hF := Ffast_ge_two_pow_two_mul x (by omega)
  have hpow : (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by rw [mul_comm, pow_mul]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ x := by positivity
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ (2 * x) := by positivity
  have hbound : (2 : ℝ) ^ x * (1 / Real.log (Ffast x) + 1 / (Ffast x : ℝ))
      ≤ (2 : ℝ) ^ x * (1 / (2 : ℝ) ^ (2 * x) + 1 / (2 : ℝ) ^ (2 * x)) := by
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (le_of_lt hpos)
    · exact one_div_le_one_div_of_le hp2 hlog
    · exact one_div_le_one_div_of_le hp2 hF
  have hfinal : (2 : ℝ) ^ x * (1 / (2 : ℝ) ^ (2 * x) + 1 / (2 : ℝ) ^ (2 * x)) ≤ η := by
    rw [hpow]
    have h2 : (2 : ℝ) ^ x * (1 / ((2 : ℝ) ^ x) ^ 2 + 1 / ((2 : ℝ) ^ x) ^ 2)
        = 2 / (2 : ℝ) ^ x := by
      field_simp
      ring
    rw [h2, div_le_iff₀ hpos]
    have hηx : 4 ≤ η * (2 : ℝ) ^ x := by
      have h := mul_le_mul_of_nonneg_left h2x hη.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hη)] at h
    linarith
  linarith [hbound, hfinal]


/-! ## The construction -/

variable {d : ℕ}

/-- The initial σ-algebra of the regularity lemma: the trivial partition refined by the
edge set `E e`. -/
noncomputable def BdOf {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (E : Finset (Fin (d+1)) → Finset (Pt V)) : Finset (Fin (d+1)) → SigAlg (Pt V) :=
  fun e => if h : e.card = d then SigAlg.triv.addSet (E e) else SigAlg.triv

@[simp] theorem BdOf_of_card_eq {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] {E : Finset (Fin (d+1)) → Finset (Pt V)}
    {e : Finset (Fin (d+1))} (h : e.card = d) :
    BdOf E e = SigAlg.triv.addSet (E e) := dif_pos h

@[simp] theorem BdOf_of_card_ne {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] {E : Finset (Fin (d+1)) → Finset (Pt V)}
    {e : Finset (Fin (d+1))} (h : e.card ≠ d) : BdOf E e = SigAlg.triv := dif_neg h

/-- The set `E'_e` of Tao's construction: the complement of the bad set of `E e` together
with the bad sets of all lower-order atoms contained in `e`. -/
noncomputable def EprOf {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    [∀ i, Nonempty (V i)]
    (B B' : ℕ → Finset (Fin (d+1)) → SigAlg (Pt V)) (M : ℕ → ℕ)
    (E : Finset (Fin (d+1)) → Finset (Pt V)) (e : Finset (Fin (d+1))) : Finset (Pt V) :=
  if _ : e.card = d then
    E e \
      (badSetOf (V := V) d (BdOf E) B B' M Ffast (e.card) e (E e) ∪
        (e.powerset.filter (fun f => f.card < e.card)).biUnion (fun f =>
          ((algOf (V := V) d (BdOf E) B f).atoms).biUnion (fun Af =>
            Af ∩ badSetOf (V := V) d (BdOf E) B B' M Ffast (f.card) f Af)))
  else Finset.univ


/-! ## The pointwise atom family and the "not good implies bad" lemma -/

/-- The pointwise atom family determined by a point `x`: at the top faces (`|f| = d`) it is
the edge set `E f`, at lower faces the atom of `x`. -/
noncomputable def AtilOf {d : ℕ} {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] (B : ℕ → Finset (Fin (d+1)) → SigAlg (Pt V))
    (E : Finset (Fin (d+1)) → Finset (Pt V)) (x : Pt V) :
    Finset (Fin (d+1)) → Finset (Pt V) :=
  fun f => if h : f.card = d then E f else (algOf (V := V) d (BdOf E) B f).block x

@[simp] theorem AtilOf_of_card_eq {d : ℕ} {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] {B : ℕ → Finset (Fin (d+1)) → SigAlg (Pt V)}
    {E : Finset (Fin (d+1)) → Finset (Pt V)} {x : Pt V} {f : Finset (Fin (d+1))}
    (h : f.card = d) : AtilOf B E x f = E f := dif_pos h

@[simp] theorem AtilOf_of_card_ne {d : ℕ} {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] {B : ℕ → Finset (Fin (d+1)) → SigAlg (Pt V)}
    {E : Finset (Fin (d+1)) → Finset (Pt V)} {x : Pt V} {f : Finset (Fin (d+1))}
    (h : f.card ≠ d) : AtilOf B E x f = (algOf (V := V) d (BdOf E) B f).block x := dif_neg h

/-- **An atom family that is not good is bad.**  If the atom family `A` fails Tao's good-atom
conditions at a face `e`, then every point lying in all the strictly smaller atoms lies in the
bad set of `e`. -/
theorem not_goodAt_mem_badSet {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]
    {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ} {F : ℕ → ℕ} {d : ℕ}
    (hHd : ∀ e ∈ Hd, e.card = d)
    {A : Finset ι → Finset (Pt V)}
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    {e : Finset ι} (he : e ∈ Hall Hd)
    (hbad : ¬ GoodAt (V := V) d Bd B B' M F A e.card e)
    {y : Pt V} (hy : ∀ g : Finset ι, g ⊆ e → g.card < e.card → y ∈ A g) :
    y ∈ badSetOf (V := V) d Bd B B' M F e.card e (A e) := by
  have hcard : e.card ≤ d := Hall_card_le hHd he
  have hblk : ∀ f : {f : Finset ι // f ∈ del e},
      (bdryAlg (V := V) B e.card e f).block y = A f.val := by
    intro f
    have hfe : f.val ⊆ e := (mem_del.mp f.2).1
    have hfcard : f.val.card + 1 = e.card := (mem_del.mp f.2).2
    have hlt : f.val.card < e.card := by omega
    have hfHall : f.val ∈ Hall Hd := Hall_down he hfe
    have hlt2 : f.val.card < d := by omega
    have hatom : A f.val ∈ (B f.val.card f.val).atoms := by
      rw [← algOf_eq_B (V := V) (Bd := Bd) (B := B) hlt2]
      exact hAtom f.val hfHall
    show (B (e.card - 1) f.val).block y = A f.val
    rw [show e.card - 1 = f.val.card from by omega]
    exact eq_of_mem_atoms hatom (hy f.val hfe hlt)
  have hlblk : ∀ f : {f : Finset ι // f ⊂ e},
      (lowAlg (V := V) B e f).block y = A f.val := by
    intro f
    have hsub : f.val ⊆ e := f.2.1
    have hlt : f.val.card < e.card := Finset.card_lt_card f.2
    have hfHall : f.val ∈ Hall Hd := Hall_down he hsub
    have hlt2 : f.val.card < d := by omega
    have hatom : A f.val ∈ (B f.val.card f.val).atoms := by
      rw [← algOf_eq_B (V := V) (Bd := Bd) (B := B) hlt2]
      exact hAtom f.val hfHall
    exact eq_of_mem_atoms hatom (hy f.val hsub hlt)
  rw [GoodAt] at hbad
  have hcases : ¬ LargeOk F M e.card (fun i : {f : Finset ι // f ∈ del e} => A i.val) (A e)
      ∨ ¬ RegOk F M e.card (fun i : {f : Finset ι // f ⊂ e} => A i.val) (A e)
          (bdryAlg (V := V) B e.card e) (bdryAlg (V := V) B' e.card e) := by
    by_cases hL : LargeOk F M e.card (fun i : {f : Finset ι // f ∈ del e} => A i.val) (A e)
    · right
      intro hR
      exact hbad ⟨hL, hR⟩
    · left; exact hL
  rcases hcases with hL | hR
  · refine Finset.mem_union_left _ ?_
    rw [mem_lBadSet]
    have hfun : (fun i : {f : Finset ι // f ∈ del e} =>
        (bdryAlg (V := V) B e.card e i).block y) = fun i => A i.val := funext hblk
    rw [hfun]
    exact hL
  · refine Finset.mem_union_right _ ?_
    rw [mem_rBadSet]
    have hfun : (fun i : {f : Finset ι // f ⊂ e} => (lowAlg (V := V) B e i).block y)
        = fun i => A i.val := funext hlblk
    rw [hfun]
    exact hR

/-! ## The construction -/

section Main

variable {d : ℕ}

theorem triv_refines {Ω : Type*} [Fintype Ω] (P : SigAlg Ω) :
    (SigAlg.triv : SigAlg Ω).Refines P :=
  fun _ => Finset.subset_univ _

theorem mem_atoms_addSet_self {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {E : Finset Ω} (hE : E.Nonempty) : E ∈ (SigAlg.triv.addSet E).atoms := by
  obtain ⟨x, hx⟩ := hE
  refine mem_atoms.mpr ⟨x, ?_⟩
  rw [SigAlg.addSet_block_of_mem _ _ hx, SigAlg.triv_block, Finset.univ_inter]

/-- The lift of a `coord g`-measurable set along the identity bundle is contained in it. -/
theorem liftSet_id_subset {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]
    {g : Finset ι} {A : Finset (Pt V)}
    (hinj : ∀ a ∈ g, ∀ b ∈ g, (id : ι → ι) a = (id : ι → ι) b → a = b)
    (hA : (coord (V := V) g).IsMeas A) :
    liftSet (V := V) (id : ι → ι) g hinj A ⊆ A := by
  intro v hv
  rw [mem_liftSet_iff] at hv
  obtain ⟨x, hxA, hxv⟩ := hv
  refine (coord_isMeas_iff.mp hA) x v (fun i hi => (hxv i hi).symm) |>.mpr hxA

theorem mem_Hall_self {ι : Type*} [DecidableEq ι] {Hd : Finset (Finset ι)} {e : Finset ι}
    (he : e ∈ Hd) : e ∈ Hall Hd := mem_Hall.mpr ⟨e, he, subset_rfl⟩

theorem sdiff_self_avg {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {S : Finset Ω} {c : ℝ} (hc : 0 ≤ c) : avg (SigAlg.indicator (S \ S)) ≤ c := by
  rw [Finset.sdiff_self]
  have : SigAlg.indicator (∅ : Finset Ω) = fun _ => (0 : ℝ) := by
    funext x; rw [SigAlg.indicator, if_neg (Finset.notMem_empty x)]
  rw [this, avg_const]
  exact hc

end Main


/-! ## The error bound for the removal step -/

/-- Averaging a finite sum. -/
theorem avg_sum_finset {β Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [DecidableEq β]
    (s : Finset β) (g : β → Ω → ℝ) :
    avg (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, avg (g i) := by
  classical
  induction s using Finset.induction with
  | empty => exact avg_const 0
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [show (fun x => ∑ i ∈ insert a s, g i x) = fun x => g a x + ∑ i ∈ s, g i x from by
        funext x; rw [Finset.sum_insert ha]]
      rw [avg_add, ih]

/-- The bad-set bound at the empty face; here the boundary and lower-order index types are
empty, so the regularity condition holds automatically. -/
theorem good_atom_bad_le_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]
    {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ} {F : ℕ → ℕ} {Ae : Finset (Pt V)}
    (hF1 : 1 ≤ F (M 0)) :
    avg (fun x => SigAlg.indicator Ae x
        * SigAlg.indicator (badSetOf (V := V) 0 (fun _ => SigAlg.triv) B B' M F 0
            (∅ : Finset ι) Ae) x)
      ≤ 1 / Real.log (F (M 0)) + 1 / (F (M 0) : ℝ) := by
  classical
  haveI : IsEmpty {f : Finset ι // f ∈ del (∅ : Finset ι)} :=
    ⟨fun x => by have h := (mem_del.mp x.2).2; simp at h⟩
  have htriv : ∀ R : {f : Finset ι // f ∈ del (∅ : Finset ι)} → SigAlg (Pt V),
      SigAlg.iInf R Finset.univ = (SigAlg.triv : SigAlg (Pt V)) := by
    intro R
    refine SigAlg.ext (fun x => ?_)
    rw [SigAlg.iInf_block, Finset.univ_eq_empty, Finset.inf_empty, SigAlg.triv_block]
    rfl
  have hlb := avg_indicator_lBad_le F M 0 Ae (bdryAlg (V := V) B 0 (∅ : Finset ι)) hF1
  have hrb := avg_indicator_rBad_le F M 0 Ae (bdryAlg (V := V) B 0 (∅ : Finset ι))
    (bdryAlg (V := V) B' 0 (∅ : Finset ι)) (lowAlg (V := V) B (∅ : Finset ι)) hF1
    (fun f => isEmptyElim f) (by
      rw [htriv (bdryAlg (V := V) B' 0 (∅ : Finset ι)),
        htriv (bdryAlg (V := V) B 0 (∅ : Finset ι))]
      nlinarith [sq_nonneg (1 / (F (M 0)) : ℝ)])
  exact avg_indicator_bad_le F M 0 Ae _ _ _ hF1 hlb hrb


/-- **The error bound for the removal step.**  The measure of the deleted part
`E_e \ E'_e` is bounded by the sum of the bad-set measures over the face `e` and over all
its proper sub-faces, each multiplied by the number of atoms. -/
theorem EprOf_avg_le {d : ℕ} (hd : 1 ≤ d) {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]
    {Md : ℕ} {B B' : ℕ → Finset (Fin (d+1)) → SigAlg (Pt V)} {M : ℕ → ℕ}
    {E : Finset (Fin (d+1)) → Finset (Pt V)} {ε : ℝ} (hε : 0 < ε)
    (hR : RegOK2 (V := V) d (HdC d) (BdOf E) Md Ffast B B' M)
    (hFdeg : ∀ j ≤ d, 1 ≤ Ffast (M j))
    (hMlow : ∀ j ≤ d, 8 ≤ M j)
    (hEne : ∀ e ∈ HdC d, E e ≠ ∅)
    (hsmall : ∀ j ≤ d, (2 : ℝ) ^ (M j)
        * (1 / Real.log (Ffast (M j)) + 1 / (Ffast (M j) : ℝ)) ≤ ε / 2 ^ (d + 3))
    {e : Finset (Fin (d+1))} (he : e.card = d) :
    avg (SigAlg.indicator (E e \ EprOf B B' M E e)) ≤ ε := by
  classical
  have hHdC : ∀ e ∈ HdC d, e.card = d := fun e he => mem_HdC.mp he
  have hmax : ∀ f ∈ Hall (HdC d), f.card ≤ d := fun f hf => hall_HdC_iff.mp hf
  have hEne' : E e ≠ ∅ := hEne e (mem_HdC.mpr he)
  have hEe : E e ∈ (BdOf E e).atoms := by
    rw [BdOf_of_card_eq he]
    exact mem_atoms_addSet_self (Finset.nonempty_iff_ne_empty.mpr hEne')
  set s : Finset (Finset (Fin (d+1))) := e.powerset.filter (fun f => f.card < e.card) with hsdef
  set B0 : Finset (Pt V) := badSetOf (V := V) d (BdOf E) B B' M Ffast e.card e (E e) with hB0def
  set B1 : Finset (Pt V) := s.biUnion
      (fun f => ((algOf (V := V) d (BdOf E) B f).atoms).biUnion
        (fun Af => Af ∩ badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af)) with hB1def
  have hEpr : EprOf B B' M E e = E e \ (B0 ∪ B1) := by
    rw [EprOf, dif_pos he, ← hsdef, ← hB0def, ← hB1def]
  have hsub : E e \ EprOf B B' M E e = E e ∩ (B0 ∪ B1) := by
    rw [hEpr]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    tauto
  have hnn : ∀ j ≤ d, 0 ≤ 1 / Real.log (Ffast (M j)) + 1 / (Ffast (M j) : ℝ) := by
    intro j hj
    have h1 : (0 : ℝ) < Real.log (Ffast (M j)) := by
      refine Real.log_pos ?_
      have h2 : 1 ≤ M j := by have := hMlow j hj; omega
      have h3 : 2 ≤ Ffast (M j) := le_trans (by omega : 2 ≤ M j + 1) (Ffast_grow (M j))
      exact_mod_cast (by omega : 1 < Ffast (M j))
    have h2 : (0 : ℝ) < (Ffast (M j) : ℝ) := by
      have h3 : 1 ≤ Ffast (M j) := hFdeg j hj
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h3)
    positivity
  have hpt : ∀ x : Pt V, SigAlg.indicator (E e \ EprOf B B' M E e) x
      ≤ SigAlg.indicator (E e) x * SigAlg.indicator B0 x + SigAlg.indicator B1 x := by
    intro x
    by_cases hx : x ∈ E e \ EprOf B B' M E e
    · have hx' : x ∈ E e ∧ x ∈ (B0 ∪ B1) := by
        rw [hsub] at hx
        exact Finset.mem_inter.mp hx
      have hidx : SigAlg.indicator (E e \ EprOf B B' M E e) x = 1 := by
        rw [SigAlg.indicator, if_pos hx]
      rw [hidx]
      rcases Finset.mem_union.mp hx'.2 with h | h
      · have h1 : SigAlg.indicator (E e) x * SigAlg.indicator B0 x = 1 := by
          rw [SigAlg.indicator, SigAlg.indicator, if_pos hx'.1, if_pos h, mul_one]
        rw [h1]
        linarith [SigAlg.indicator_nonneg B1 x]
      · have h1 : SigAlg.indicator B1 x = 1 := by rw [SigAlg.indicator, if_pos h]
        rw [h1]
        linarith [mul_nonneg (SigAlg.indicator_nonneg (E e) x) (SigAlg.indicator_nonneg B0 x)]
    · have hidx : SigAlg.indicator (E e \ EprOf B B' M E e) x = 0 := by
        rw [SigAlg.indicator, if_neg hx]
      rw [hidx]
      linarith [mul_nonneg (SigAlg.indicator_nonneg (E e) x) (SigAlg.indicator_nonneg B0 x),
        SigAlg.indicator_nonneg B1 x]
  have hT1 : avg (fun x => SigAlg.indicator (E e) x * SigAlg.indicator B0 x) ≤ ε / 2 ^ (d + 3) := by
    have hAe : E e ∈ (edgeAlg (V := V) (BdOf E) B d d e).atoms := by
      simpa [edgeAlg] using hEe
    have hgood := good_atom_bad_le_RegOK2 (V := V) (d := d) (Hd := HdC d) (Bd := BdOf E) (Md := Md)
      (F := Ffast) (B := B) (B' := B') (M := M) hR (j := d) hd le_rfl
      (by rw [Nat.sub_self]; exact mem_HdC.mpr he) hAe (hFdeg d le_rfl)
    have hB0 : B0 = badSetOf (V := V) d (BdOf E) B B' M Ffast d e (E e) := by
      rw [hB0def, he]
    rw [hB0]
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (M d) := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact le_trans hgood (le_trans (le_mul_of_one_le_left (hnn d le_rfl) hp) (hsmall d le_rfl))
  have hatom : ∀ f ∈ s, ∀ Af ∈ (algOf (V := V) d (BdOf E) B f).atoms,
      avg (fun x => SigAlg.indicator Af x
          * SigAlg.indicator (badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af) x)
        ≤ 1 / Real.log (Ffast (M f.card)) + 1 / (Ffast (M f.card) : ℝ) := by
    intro f hf Af hAf
    have hfe : f ⊆ e := Finset.mem_powerset.mp (Finset.mem_filter.mp hf).1
    have hfle : f.card ≤ d := by
      have := Finset.card_le_card hfe
      rw [he] at this; exact this
    by_cases hf0 : f.card = 0
    · have hfz : f = ∅ := Finset.card_eq_zero.mp hf0
      rw [hfz] at hAf ⊢
      have h := good_atom_bad_le_zero (V := V) (B := B) (B' := B') (M := M) (F := Ffast)
        (Ae := Af) (hFdeg 0 (Nat.zero_le d))
      simpa using h
    · have hf1 : 1 ≤ f.card := Nat.one_le_iff_ne_zero.mpr hf0
      have hlev : f ∈ lev (HdC d) (d - f.card) :=
        Hall_mem_lev hHdC (hall_HdC hfle)
      have hAe : Af ∈ (edgeAlg (V := V) (BdOf E) B d f.card f).atoms := hAf
      exact good_atom_bad_le_RegOK2 (V := V) (d := d) (Hd := HdC d) (Bd := BdOf E) (Md := Md)
        (F := Ffast) (B := B) (B' := B') (M := M) hR hf1 hfle hlev hAe (hFdeg f.card hfle)
  have hatomcard : ∀ f ∈ s, ((algOf (V := V) d (BdOf E) B f).atoms.card : ℕ)
      ≤ 2 ^ (M f.card) := by
    intro f hf
    have hfe : f ⊆ e := Finset.mem_powerset.mp (Finset.mem_filter.mp hf).1
    have hfle : f.card ≤ d := by
      have := Finset.card_le_card hfe
      rw [he] at this; exact this
    by_cases hfd : f.card = d
    · have h1 : algOf (V := V) d (BdOf E) B f = BdOf E f := by
        simp only [algOf, edgeAlg]
        rw [if_pos hfd]
      rw [h1, BdOf_of_card_eq hfd]
      have h2 := SigAlg.atoms_addSet_card_le (SigAlg.triv : SigAlg (Pt V)) (E f)
      have h3 : (SigAlg.triv : SigAlg (Pt V)).atoms.card ≤ 1 := by
        rw [SigAlg.atoms]
        refine le_trans (Finset.card_le_one.mpr ?_) le_rfl
        intro a ha b hb
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
        simp
      have h4 : M f.card = M d := by rw [hfd]
      rw [h4]
      have h5 : 1 ≤ M d := by have := hMlow d le_rfl; omega
      have h6 : 2 ≤ 2 ^ (M d) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (M d) := Nat.pow_le_pow_right (by norm_num) h5
      omega
    · have h1 : algOf (V := V) d (BdOf E) B f = B f.card f :=
        algOf_eq_B (V := V) (Bd := BdOf E) (B := B) (by omega : f.card < d)
      rw [h1]
      have h2 : (B f.card f).complexity ≤ M f.card :=
        hR.2.2.2.2.2.2.1 f.card (by omega) f (Hall_mem_lev hHdC (hall_HdC hfle))
      exact le_trans (SigAlg.atoms_card_le_pow_complexity (B f.card f))
        (Nat.pow_le_pow_right (by norm_num) h2)
  have hT2 : avg (fun x => SigAlg.indicator B1 x) ≤ ε / 8 := by
    have hpt2 : ∀ x : Pt V, SigAlg.indicator B1 x
        ≤ ∑ f ∈ s, ∑ Af ∈ (algOf (V := V) d (BdOf E) B f).atoms,
            SigAlg.indicator Af x
              * SigAlg.indicator (badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af) x := by
      intro x
      by_cases hx : x ∈ B1
      · have hidx : SigAlg.indicator B1 x = 1 := by rw [SigAlg.indicator, if_pos hx]
        rw [hidx]
        have hex : ∃ f ∈ s, ∃ Af ∈ (algOf (V := V) d (BdOf E) B f).atoms,
            x ∈ Af ∩ badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af := by
          rw [hB1def, Finset.mem_biUnion] at hx
          obtain ⟨f, hf, hx⟩ := hx
          rw [Finset.mem_biUnion] at hx
          exact ⟨f, hf, hx⟩
        obtain ⟨f, hf, Af, hAf, hx'⟩ := hex
        have hinner : SigAlg.indicator Af x
              * SigAlg.indicator (badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af) x
            ≤ ∑ Af' ∈ (algOf (V := V) d (BdOf E) B f).atoms,
                SigAlg.indicator Af' x
                  * SigAlg.indicator
                      (badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af') x :=
          Finset.single_le_sum
            (f := fun Af' => SigAlg.indicator Af' x
              * SigAlg.indicator (badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af') x)
            (fun Af' _ => mul_nonneg (SigAlg.indicator_nonneg _ x) (SigAlg.indicator_nonneg _ x))
            hAf
        have hstep : SigAlg.indicator Af x
            * SigAlg.indicator (badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af) x = 1 := by
          have h1 : x ∈ Af := (Finset.mem_inter.mp hx').1
          have h2 : x ∈ badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af :=
            (Finset.mem_inter.mp hx').2
          rw [SigAlg.indicator, SigAlg.indicator, if_pos h1, if_pos h2, mul_one]
        rw [hstep] at hinner
        exact le_trans hinner
          (Finset.single_le_sum
            (f := fun f' => ∑ Af' ∈ (algOf (V := V) d (BdOf E) B f').atoms,
                SigAlg.indicator Af' x
                  * SigAlg.indicator (badSetOf (V := V) d (BdOf E) B B' M Ffast f'.card f' Af') x)
            (fun f' _ => Finset.sum_nonneg fun Af' _ =>
              mul_nonneg (SigAlg.indicator_nonneg _ x) (SigAlg.indicator_nonneg _ x)) hf)
      · have hidx : SigAlg.indicator B1 x = 0 := by rw [SigAlg.indicator, if_neg hx]
        rw [hidx]
        exact Finset.sum_nonneg (fun f _ => Finset.sum_nonneg fun Af _ =>
          mul_nonneg (SigAlg.indicator_nonneg _ x) (SigAlg.indicator_nonneg _ x))
    have hsum1 : avg (fun x => ∑ f ∈ s, ∑ Af ∈ (algOf (V := V) d (BdOf E) B f).atoms,
        SigAlg.indicator Af x
          * SigAlg.indicator (badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af) x)
        = ∑ f ∈ s, ∑ Af ∈ (algOf (V := V) d (BdOf E) B f).atoms,
            avg (fun x => SigAlg.indicator Af x
              * SigAlg.indicator (badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af) x) := by
      rw [avg_sum_finset]
      refine Finset.sum_congr rfl (fun f _ => ?_)
      rw [avg_sum_finset]
    calc avg (fun x => SigAlg.indicator B1 x)
        ≤ avg (fun x => ∑ f ∈ s, ∑ Af ∈ (algOf (V := V) d (BdOf E) B f).atoms,
            SigAlg.indicator Af x
              * SigAlg.indicator (badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af) x) :=
          avg_le_avg hpt2
      _ = _ := hsum1
      _ ≤ ∑ f ∈ s, ∑ Af ∈ (algOf (V := V) d (BdOf E) B f).atoms,
            (1 / Real.log (Ffast (M f.card)) + 1 / (Ffast (M f.card) : ℝ)) :=
          Finset.sum_le_sum (fun f hf => Finset.sum_le_sum (fun Af hAf => hatom f hf Af hAf))
      _ = ∑ f ∈ s, (((algOf (V := V) d (BdOf E) B f).atoms.card : ℕ) : ℝ)
            * (1 / Real.log (Ffast (M f.card)) + 1 / (Ffast (M f.card) : ℝ)) := by
          refine Finset.sum_congr rfl (fun f _ => ?_)
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ f ∈ s, ε / 2 ^ (d + 3) := by
          refine Finset.sum_le_sum (fun f hf => ?_)
          have hfe : f ⊆ e := Finset.mem_powerset.mp (Finset.mem_filter.mp hf).1
          have hfle : f.card ≤ d := by
            have := Finset.card_le_card hfe
            rw [he] at this; exact this
          have hcard := hatomcard f hf
          have hcardR : (((algOf (V := V) d (BdOf E) B f).atoms.card : ℕ) : ℝ)
              ≤ (2 : ℝ) ^ (M f.card) := by
            calc (((algOf (V := V) d (BdOf E) B f).atoms.card : ℕ) : ℝ)
                ≤ ((2 ^ (M f.card) : ℕ) : ℝ) := by exact_mod_cast hcard
              _ = (2 : ℝ) ^ (M f.card) := by push_cast; ring
          exact le_trans (mul_le_mul_of_nonneg_right hcardR (hnn f.card hfle))
            (hsmall f.card hfle)
      _ = ((s.card : ℕ) : ℝ) * (ε / 2 ^ (d + 3)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ d * (ε / 2 ^ (d + 3)) := by
          have hcard : s.card ≤ 2 ^ d := by
            calc s.card ≤ e.powerset.card := Finset.card_filter_le _ _
              _ = 2 ^ e.card := Finset.card_powerset e
              _ = 2 ^ d := by rw [he]
          have h1 : ((s.card : ℕ) : ℝ) ≤ (2 : ℝ) ^ d := by
            calc ((s.card : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) := by exact_mod_cast hcard
              _ = (2 : ℝ) ^ d := by push_cast; ring
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ε / 8 := by
          rw [show (2 : ℝ) ^ (d + 3) = 8 * (2 : ℝ) ^ d by rw [pow_add]; ring]
          rw [show (2 : ℝ) ^ d * (ε / (8 * 2 ^ d)) = ε / 8 by field_simp]
  have hmain : avg (fun x => SigAlg.indicator (E e \ EprOf B B' M E e) x)
      ≤ ε / 2 ^ (d + 3) + ε / 8 := by
    refine le_trans (avg_le_avg hpt) ?_
    rw [avg_add]
    exact add_le_add hT1 hT2
  have h8 : ε / 2 ^ (d + 3) ≤ ε / 8 := by
    rw [show (2 : ℝ) ^ (d + 3) = 2 ^ d * 2 ^ 3 by rw [pow_add]]
    have h1 : (8 : ℝ) ≤ 2 ^ d * 2 ^ 3 := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
      nlinarith
    exact div_le_div_of_nonneg_left hε.le (by norm_num) h1
  linarith


/-! ## Measurability of `E'`, and the emptiness argument -/

theorem SigAlg.IsMeas.biUnion {κ : Type*} [DecidableEq κ]
    {P : SigAlg (Pt V)} {s : Finset κ} {f : κ → Finset (Pt V)}
    (h : ∀ i ∈ s, P.IsMeas (f i)) : P.IsMeas (s.biUnion f) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (SigAlg.isMeas_empty (P := P))
  | insert a s ha ih =>
      rw [Finset.biUnion_insert]
      exact (h a (Finset.mem_insert_self a s)).union
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `E'_e` is measurable for the coordinate σ-algebra of `e`. -/
theorem EprOf_isMeas_coord {d : ℕ} {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]
    {Md : ℕ} {B B' : ℕ → Finset (Fin (d+1)) → SigAlg (Pt V)} {M : ℕ → ℕ}
    {E : Finset (Fin (d+1)) → Finset (Pt V)}
    (hEmeas : ∀ e : Finset (Fin (d+1)), e.card = d → (coord (V := V) e).IsMeas (E e))
    (hBd : ∀ e ∈ HdC d, (BdOf E e).Refines (coord (V := V) e))
    (hR : RegOK2 (V := V) d (HdC d) (BdOf E) Md Ffast B B' M)
    {e : Finset (Fin (d+1))} (he : e.card = d) :
    (coord (V := V) e).IsMeas (EprOf B B' M E e) := by
  classical
  have hHdC : ∀ e ∈ HdC d, e.card = d := fun e he => mem_HdC.mp he
  have halgRef : ∀ f ∈ Hall (HdC d), (algOf (V := V) d (BdOf E) B f).Refines
      (coord (V := V) f) := fun f hf => algOf_refines_coord hHdC hBd hR hf
  have hB0 : (coord (V := V) e).IsMeas
      (badSetOf (V := V) d (BdOf E) B B' M Ffast e.card e (E e)) :=
    badSetOf_isMeas_coord (V := V) hHdC hR (hall_HdC (by omega)) rfl (subset_rfl) _
  have hB1 : (coord (V := V) e).IsMeas
      ((e.powerset.filter (fun f => f.card < e.card)).biUnion (fun f =>
        ((algOf (V := V) d (BdOf E) B f).atoms).biUnion (fun Af =>
          Af ∩ badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af))) := by
    refine SigAlg.IsMeas.biUnion (s := e.powerset.filter (fun f => f.card < e.card))
      (f := fun f => ((algOf (V := V) d (BdOf E) B f).atoms).biUnion (fun Af =>
          Af ∩ badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af)) (fun f hf => ?_)
    have hfe : f ⊆ e := Finset.mem_powerset.mp (Finset.mem_filter.mp hf).1
    have hfle : f.card ≤ d := by
      have := Finset.card_le_card hfe
      rw [he] at this; exact this
    have hfHall : f ∈ Hall (HdC d) := hall_HdC hfle
    refine SigAlg.IsMeas.biUnion (s := (algOf (V := V) d (BdOf E) B f).atoms)
      (f := fun Af => Af ∩ badSetOf (V := V) d (BdOf E) B B' M Ffast f.card f Af)
      (fun Af hAf => ?_)
    refine (coord_isMeas_of_subset hfe ?_).inter
      (badSetOf_isMeas_coord (V := V) hHdC hR hfHall rfl hfe _)
    exact (IsMeas_of_mem_atoms hAf).of_refines (halgRef f hfHall)
  rw [EprOf, dif_pos he]
  exact (hEmeas e he).sdiff (hB0.union hB1)

/-- **Emptiness of the intersection**: if every `E'_e` contains `x`, we get a contradiction
with the counting lemma. -/
theorem EprOf_empty {d : ℕ} (hd : 1 ≤ d) {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]
    {Md : ℕ} {B B' : ℕ → Finset (Fin (d+1)) → SigAlg (Pt V)} {M : ℕ → ℕ}
    {E : Finset (Fin (d+1)) → Finset (Pt V)}
    (hBd : ∀ e ∈ HdC d, (BdOf E e).Refines (coord (V := V) e))
    (hR : RegOK2 (V := V) d (HdC d) (BdOf E) Md Ffast B B' M)
    (hnoGood : ∀ A : Finset (Fin (d+1)) → Finset (Pt V),
        (∀ f ∈ Hall (HdC d), A f ∈ (algOf (V := V) d (BdOf E) B f).atoms) →
        (∀ e ∈ HdC d, A e = E e) →
        ¬ (∀ e ∈ Hall (HdC d), GoodAt (V := V) d (BdOf E) B B' M Ffast A e.card e))
    {x : Pt V} (hx : ∀ e ∈ HdC d, x ∈ EprOf B B' M E e) : False := by
  classical
  have hHdC : ∀ e ∈ HdC d, e.card = d := fun e he => mem_HdC.mp he
  have hxE : ∀ e ∈ HdC d, x ∈ E e := by
    intro e he
    have h1 := hx e he
    rw [EprOf, dif_pos (hHdC e he)] at h1
    exact (Finset.mem_sdiff.mp h1).1
  have hEne : ∀ e ∈ HdC d, E e ≠ ∅ := by
    intro e he h0
    have h1 := hxE e he
    rw [h0] at h1
    exact Finset.notMem_empty x h1
  have hAtomA : ∀ f ∈ Hall (HdC d), AtilOf B E x f ∈ (algOf (V := V) d (BdOf E) B f).atoms := by
    intro f hf
    have hfle : f.card ≤ d := hall_HdC_iff.mp hf
    by_cases hfd : f.card = d
    · rw [AtilOf_of_card_eq hfd]
      have h1 : algOf (V := V) d (BdOf E) B f = BdOf E f := by
        simp only [algOf, edgeAlg]
        rw [if_pos hfd]
      rw [h1, BdOf_of_card_eq hfd]
      exact mem_atoms_addSet_self (Finset.nonempty_iff_ne_empty.mpr (hEne f (mem_HdC.mpr hfd)))
    · rw [AtilOf_of_card_ne hfd]
      exact SigAlg.block_mem_atoms _ _
  have hAeA : ∀ e ∈ HdC d, AtilOf B E x e = E e := fun e he => AtilOf_of_card_eq (hHdC e he)
  have hf'ex : ∃ f' ∈ Hall (HdC d), ¬ GoodAt (V := V) d (BdOf E) B B' M Ffast
      (AtilOf B E x) f'.card f' := by
    by_contra hcon
    refine hnoGood (AtilOf B E x) hAtomA hAeA fun e he => ?_
    by_contra hbad
    exact hcon ⟨e, he, hbad⟩
  obtain ⟨f', hf'Hall, hf'bad⟩ := hf'ex
  have hxAtil : ∀ f ∈ Hall (HdC d), x ∈ AtilOf B E x f := by
    intro f hf
    by_cases hfd : f.card = d
    · rw [AtilOf_of_card_eq hfd]
      exact hxE f (mem_HdC.mpr hfd)
    · rw [AtilOf_of_card_ne hfd]
      exact SigAlg.block_self_mem _ _
  have hysub : ∀ g : Finset (Fin (d+1)), g ⊆ f' → g.card < f'.card → x ∈ AtilOf B E x g :=
    fun g hg _ => hxAtil g (Hall_down hf'Hall hg)
  have hxbad := not_goodAt_mem_badSet (V := V) (Bd := BdOf E) (F := Ffast) hHdC hAtomA
    hf'Hall hf'bad hysub
  obtain ⟨e, he, hf'e⟩ := mem_Hall.mp hf'Hall
  have hee : e.card = d := hHdC e he
  have hxe := hx e he
  rw [EprOf, dif_pos hee] at hxe
  obtain ⟨-, hxe'⟩ := Finset.mem_sdiff.mp hxe
  rw [Finset.mem_union, not_or] at hxe'
  by_cases hfe : f' = e
  · refine hxe'.1 ?_
    have hf'Hd : f' ∈ HdC d := mem_HdC.mpr (by rw [hfe]; exact hee)
    rw [hAeA f' hf'Hd] at hxbad
    rwa [hfe] at hxbad
  · have hlt : f'.card < e.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hf'e, hfe⟩)
    refine hxe'.2 ?_
    rw [Finset.mem_biUnion]
    refine ⟨f', Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hf'e, hlt⟩, ?_⟩
    rw [Finset.mem_biUnion]
    exact ⟨AtilOf B E x f', hAtomA f' hf'Hall,
      Finset.mem_inter.mpr ⟨hxAtil f' hf'Hall, hxbad⟩⟩


theorem SigAlg.indicator_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    {E F : Finset Ω} (h : E ⊆ F)
    (x : Ω) : SigAlg.indicator E x ≤ SigAlg.indicator F x := by
  by_cases hx : x ∈ E
  · rw [SigAlg.indicator, if_pos hx, SigAlg.indicator, if_pos (h hx)]
  · rw [SigAlg.indicator, if_neg hx]
    exact SigAlg.indicator_nonneg F x

/-- The `Cnt` of the trivial bundle is at most the measure of the product of the edge sets. -/
theorem Cnt_id_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]
    (Hd : Finset (Finset ι)) (A E : Finset ι → Finset (Pt V))
    (hAmeas : ∀ f ∈ Hall Hd, (coord (V := V) f).IsMeas (A f))
    (hAE : ∀ e ∈ Hd, A e = E e) :
    Cnt (V := V) (id : ι → ι) (Hall Hd)
        (AgOf (V := V) A (id : ι → ι) (Hall Hd) (isBundle_id Hd).inj)
      ≤ avg (fun x => ∏ e ∈ Hd, SigAlg.indicator (E e) x) := by
  classical
  refine avg_le_avg (fun v => ?_)
  show (∏ g ∈ Hall Hd, SigAlg.indicator (AgOf (V := V) A (id : ι → ι) (Hall Hd)
      (isBundle_id Hd).inj g) v) ≤ _
  calc ∏ g ∈ Hall Hd, SigAlg.indicator (AgOf (V := V) A (id : ι → ι) (Hall Hd)
        (isBundle_id Hd).inj g) v
      ≤ ∏ g ∈ Hall Hd, SigAlg.indicator (A g) v := by
        refine Finset.prod_le_prod (fun g _ => SigAlg.indicator_nonneg _ _) (fun g hg => ?_)
        rw [AgOf_of_mem (V := V) A (id : ι → ι) (Hall Hd) (isBundle_id Hd).inj hg]
        simp only [Finset.image_id]
        exact SigAlg.indicator_mono (liftSet_id_subset (V := V) _ (hAmeas g hg)) v
    _ ≤ ∏ e ∈ Hd, SigAlg.indicator (A e) v :=
        Finset.prod_anti_set_of_le_one (f := fun e => SigAlg.indicator (A e) v)
          (fun e => SigAlg.indicator_nonneg _ _) (fun e => SigAlg.indicator_le_one _ _)
          (fun e he => mem_Hall_self he)
    _ = ∏ e ∈ Hd, SigAlg.indicator (E e) v :=
        Finset.prod_congr rfl (fun e he => by rw [hAE e he])

/-- **The hypergraph removal lemma** (Tao, `main-2`), for the complete `d`-uniform hypergraph
on `Fin (d+1)`. -/
theorem hypergraph_removal_complete (d : ℕ) (hd : 1 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ {V : Fin (d+1) → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
        [∀ i, Nonempty (V i)]
        (E : Finset (Fin (d+1)) → Finset (Pt V)),
        (∀ e : Finset (Fin (d+1)), e.card = d → (coord (V := V) e).IsMeas (E e)) →
        avg (fun x => ∏ e ∈ HdC d, SigAlg.indicator (E e) x) ≤ δ →
        ∃ E' : Finset (Fin (d+1)) → Finset (Pt V),
          (∀ e, e.card = d → E' e ⊆ E e) ∧
          (∀ e, e.card = d → (coord (V := V) e).IsMeas (E' e)) ∧
          (∀ e, e.card = d → avg (SigAlg.indicator (E e \ E' e)) ≤ ε) ∧
          (∀ x : Pt V, ∃ e : Finset (Fin (d+1)), e.card = d ∧ x ∉ E' e) := by
  intro ε hε
  set K : ℕ := (Hall (HdC d)).card with hKdef
  obtain ⟨T0, a, b, hT08, ha0, hb0, hTa, hTb, hTc, hη⟩ := exists_counting_threshold_Fast d K
  obtain ⟨T1, hT1⟩ := eventually_two_pow_mul_le (ε / 2 ^ (d + 3)) (by positivity)
  set Md : ℕ := max (max T0 T1) 8 with hMddef
  have hMdT0 : T0 ≤ Md := by rw [hMddef]; omega
  have hMdT1 : T1 ≤ Md := by rw [hMddef]; omega
  have hMd8 : 8 ≤ Md := by rw [hMddef]; omega
  set Lb : ℝ := Real.log (Ffast (MbddF Ffast d (HdC d) Md)) + 2 with hLbdef
  have hLbpos : 0 < Lb := by
    rw [hLbdef]
    have h1 : (0 : ℝ) ≤ Real.log (Ffast (MbddF Ffast d (HdC d) Md)) :=
      Real.log_nonneg (by exact_mod_cast (Ffast_pos _))
    linarith
  refine ⟨(1 / 8) * (1 / Lb) ^ K, by positivity, ?_⟩
  intro V _ _ _ E hEmeas hδ
  have hHdC : ∀ e ∈ HdC d, e.card = d := fun e he => mem_HdC.mp he
  by_cases hEmpty : ∃ e ∈ HdC d, E e = ∅
  · obtain ⟨e0, he0, hE0⟩ := hEmpty
    refine ⟨E, fun e _ => subset_rfl, hEmeas, fun e he => sdiff_self_avg hε.le,
      fun x => ⟨e0, mem_HdC.mp he0, ?_⟩⟩
    · rw [hE0]
      exact Finset.notMem_empty x
  · push_neg at hEmpty
    have hBdref : ∀ e ∈ HdC d, (BdOf E e).Refines (coord (V := V) e) := by
      intro e he
      rw [BdOf_of_card_eq (hHdC e he)]
      exact SigAlg.Refines.addSet_of_isMeas (triv_refines _) (hEmeas e (hHdC e he))
    have hBdc : ∀ e ∈ HdC d, (BdOf E e).complexity ≤ Md := by
      intro e he
      rw [BdOf_of_card_eq (hHdC e he)]
      have h1 := SigAlg.complexity_addSet_le (SigAlg.triv : SigAlg (Pt V)) (E e)
      have h2 : (SigAlg.triv : SigAlg (Pt V)).complexity = 0 := triv_complexity
      omega
    obtain ⟨B, B', M, hR⟩ := full_regularity2 (V := V) d (HdC d) (BdOf E) Md Ffast
      Ffast_grow Ffast_mono hBdc
    have hMd_eq : M d = Md := hR.1
    have hManti : ∀ D ≤ d, M d ≤ M D := fun D hD => hR.M_anti Ffast_grow D d hD le_rfl
    have hManti' : ∀ D ≤ d, Md ≤ M D := fun D hD => by rw [← hMd_eq]; exact hManti D hD
    have hMlow : ∀ j ≤ d, 8 ≤ M j := by
      intro j hj
      have h1 := hManti j hj
      rw [hMd_eq] at h1
      omega
    have hFdeg : ∀ j ≤ d, 1 ≤ Ffast (M j) := fun j _ => Ffast_pos _
    have hlog : ∀ e ∈ Hall (HdC d), 1 ≤ Real.log (Ffast (M e.card)) := by
      intro e he
      have hle : e.card ≤ d := hall_HdC_iff.mp he
      have h1 : 8 ≤ M e.card := hMlow e.card hle
      have h2 : (9 : ℝ) ≤ (Ffast (M e.card) : ℝ) := by
        have h3 : 9 ≤ Ffast (M e.card) := by
          have h4 := Ffast_grow (M e.card)
          omega
        exact_mod_cast h3
      refine le_trans ?_ (Real.log_le_log (by norm_num) h2)
      have hexp : Real.exp 1 < 9 := by have := Real.exp_one_lt_d9; linarith
      exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp |>.le
    have hsmall : ∀ j ≤ d, (2 : ℝ) ^ (M j)
        * (1 / Real.log (Ffast (M j)) + 1 / (Ffast (M j) : ℝ)) ≤ ε / 2 ^ (d + 3) := by
      intro j hj
      exact hT1 (M j) (le_trans hMdT1 (hManti' j hj))
    have noGood : ∀ A : Finset (Fin (d+1)) → Finset (Pt V),
        (∀ f ∈ Hall (HdC d), A f ∈ (algOf (V := V) d (BdOf E) B f).atoms) →
        (∀ e ∈ HdC d, A e = E e) →
        ¬ (∀ e ∈ Hall (HdC d), GoodAt (V := V) d (BdOf E) B B' M Ffast A e.card e) := by
      intro A hAtom hAe hGood
      have hmem : (∅ : Finset (Fin (d+1))) ∈ Hall (HdC d) := hall_HdC (by simp)
      have hempty : A ∅ = Finset.univ := by
        have hcoord : (coord (V := V) (∅ : Finset (Fin (d+1)))).IsMeas (A ∅) :=
          coord_isMeas_of_atom (V := V) hHdC hBdref hAtom hR hmem
        rw [coord_empty_eq_triv] at hcoord
        obtain ⟨y, hy⟩ := atoms_nonempty (hAtom ∅ hmem)
        refine Finset.eq_univ_iff_forall.mpr (fun x => ?_)
        exact hcoord y hy (Finset.mem_univ x)
      have hlower := counting_lemma_lower_growth_F (V := V) (Hd := HdC d) (Bd := BdOf E)
        (Md := Md) (F := Ffast) (B := B) (B' := B') (M := M) (A := A)
        hHdC hBdref hAtom hGood hR Ffast_grow Ffast_mono hlog hempty hd
        (by have := hMlow d le_rfl; omega) hManti (by rw [hMd_eq]; exact hMdT0) hT08
        ha0 hTa hb0 hTb hTc hη
      have hCnt_le := Cnt_id_le_prod (V := V) (HdC d) A E
        (fun f hf => coord_isMeas_of_atom (V := V) hHdC hBdref hAtom hR hf) hAe
      have hLup : LupC Ffast M ≤ Lb := by
        rw [hLbdef]
        unfold LupC
        have h1 : M 0 ≤ MbddF Ffast d (HdC d) Md := hR.2.1
        have h2 : Ffast (M 0) ≤ Ffast (MbddF Ffast d (HdC d) Md) := Ffast_mono h1
        have h3 : (0 : ℝ) < (Ffast (M 0) : ℝ) := by
          have := Ffast_pos (M 0); exact_mod_cast this
        have h4 : Real.log (Ffast (M 0)) ≤ Real.log (Ffast (MbddF Ffast d (HdC d) Md)) :=
          Real.log_le_log h3 (by exact_mod_cast h2)
        linarith
      have hLup0 : 0 < LupC Ffast M := by
        unfold LupC
        have h1 : (0 : ℝ) ≤ Real.log (Ffast (M 0)) :=
          Real.log_nonneg (by exact_mod_cast (Ffast_pos (M 0)))
        linarith
      have hδlt : (1 / 8) * (1 / Lb) ^ K < (1 / 4) * (1 / LupC Ffast M) ^ K := by
        have h1 : (1 : ℝ) / Lb ≤ 1 / LupC Ffast M := one_div_le_one_div_of_le hLup0 hLup
        have h2 : (1 / Lb) ^ K ≤ (1 / LupC Ffast M) ^ K :=
          pow_le_pow_left₀ (by positivity) h1 K
        have h3 : (0 : ℝ) < (1 / Lb) ^ K := by positivity
        nlinarith [h2, h3]
      linarith [hlower, hCnt_le, hδ, hδlt]
    refine ⟨EprOf B B' M E, fun e he => ?_, fun e he => ?_, fun e he => ?_, fun x => ?_⟩
    · rw [EprOf, dif_pos he]
      exact Finset.sdiff_subset
    · exact EprOf_isMeas_coord (V := V) hEmeas hBdref hR he
    · exact EprOf_avg_le (V := V) hd hε hR hFdeg hMlow
        (fun e he => Finset.nonempty_iff_ne_empty.mp (hEmpty e he)) hsmall he
    · by_contra hcon
      push_neg at hcon
      exact EprOf_empty (V := V) hd hBdref hR noGood (fun e he => hcon e (hHdC e he))

end Szemeredi.Removal
