import Mathlib
import Submission.Work.WilE6.Closure
import Submission.Work.WilE6.CritSA
import Submission.Work.WilE6.Base
import Submission.Work.WilE6.Block
import Submission.Work.WilE6.Setup
import Submission.Work.WilE6.critSA_mem_iff
import Submission.Work.WilE6.critSA_deg_le
import Submission.Work.WilE6.mem_saSlice_iff
import Submission.Work.WilE6.eaTaylor_poly_shifted
import Submission.Work.WilE6.norm_witness_iff
import Submission.Work.WilE6.critFibreCond_imp_critCond
import Submission.Work.WilE6.critCond_imp_exists_witness
import Submission.Work.WilE6.FrozenCrit
import Submission.Work.WilE6.critFibreCond_bound
import Submission.Work.WilE6.critUnion_deg_le

noncomputable section
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

@[simp] theorem projU_zero (k p : ℕ) : projU k p (0 : Fin (FQ k p) → ℝ) = 0 := by
  funext i; rfl

theorem continuous_projU (k p : ℕ) : Continuous (projU k p) := by
  rw [continuous_pi_iff]
  intro i
  exact continuous_apply (fU k p i)

section Assembly

variable {r p q : ℕ}

/-- The criterion set of a single basic set, in the fibre coordinates `u`. -/
def critSet (hp : p ≤ p + q) (κ : ℕ) (c : EAChain (p + q) r) (B : Basic (p + q) r)
    (z : Fin (p + q) → ℝ) : Set (Fin (p + q) → ℝ) :=
  {u | critCond (p := p) hp κ (Pof c B κ) (Gsof c B κ) z (hvec c z) u}

variable {k : ℕ}

/-- The graph point, viewed as a point of `Fin (BP k r)` (so that `Fin.append` splits at
`BP k r` syntactically). -/
def gpBP (c : EAChain k r) (z : Fin k → ℝ) : Fin (BP k r) → ℝ := graphPt c z

theorem gpBP_castAdd (c : EAChain k r) (z : Fin k → ℝ) (i : Fin k) :
    gpBP c z (Fin.castAdd r i) = z i := by
  rw [gpBP]; exact graphPt_castAdd c z i

theorem gpBP_natAdd (c : EAChain k r) (z : Fin k → ℝ) (j : Fin r) :
    gpBP c z (Fin.natAdd k j) = hvec c z j := by
  rw [gpBP]; exact graphPt_natAdd c z j

theorem appPt_idxZ (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) (i : Fin k) :
    Fin.append (gpBP c z) v (idxZ k r p i) = z i := by
  have h1 : idxZ k r p i = Fin.castAdd (FQ k p)
      (⟨i.1, by simp only [BP]; omega⟩ : Fin (BP k r)) := Fin.ext rfl
  rw [h1, Fin.append_left]
  rw [show (⟨i.1, by simp only [BP]; omega⟩ : Fin (BP k r)) = Fin.castAdd r i from
    Fin.ext rfl, gpBP_castAdd]

theorem appPt_idxH (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) (j : Fin r) :
    Fin.append (gpBP c z) v (idxH k r p j) = hvec c z j := by
  have h1 : idxH k r p j = Fin.castAdd (FQ k p)
      (⟨k + j.1, by simp only [BP]; omega⟩ : Fin (BP k r)) := Fin.ext rfl
  rw [h1, Fin.append_left]
  rw [show (⟨k + j.1, by simp only [BP]; omega⟩ : Fin (BP k r)) = Fin.natAdd k j from
    Fin.ext rfl, gpBP_natAdd]

theorem appPt_idxU (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) (i : Fin k) :
    Fin.append (gpBP c z) v (idxU k r p i) = v (fU k p i) := by
  rw [idxU_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

theorem appPt_idxT (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) :
    Fin.append (gpBP c z) v (idxT k r p) = v (fT k p) := by
  rw [idxT_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

theorem appPt_idxWm (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) (i : Fin k) :
    Fin.append (gpBP c z) v (idxWm k r p i) = v (fWm k p i) := by
  rw [idxWm_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

theorem appPt_idxW0 (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) :
    Fin.append (gpBP c z) v (idxW0 k r p) = v (fW0 k p) := by
  rw [idxW0_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

theorem appPt_idxWb (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ)
    (b : Fin (2 * p)) :
    Fin.append (gpBP c z) v (idxWb k r p b) = v (fWb k p b) := by
  rw [idxWb_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

theorem appPt_idxWe (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) (e : Fin 2) :
    Fin.append (gpBP c z) v (idxWe k r p e) = v (fWe k p e) := by
  rw [idxWe_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

/-- The witness set: the fibre of `critSA` for the basic set `B` at the point `z`. -/
def uSet (hp : p ≤ p + q) (κ : ℕ) (c : EAChain (p + q) r) (B : Basic (p + q) r)
    (z : Fin (p + q) → ℝ) : Set (Fin (FQ (p + q) p) → ℝ) :=
  {v | ∃ j : Fin (p + q + 1),
    critFibreCond (p := p) hp κ (Pof c B κ) (Gsof c B κ) j (Fin.append (gpBP c z) v)}

theorem critCond_witness (hp : p ≤ p + q) {κ : ℕ} (hκ : 1 ≤ κ) (c : EAChain (p + q) r)
    (B : Basic (p + q) r) (z u : Fin (p + q) → ℝ)
    (h : u ∈ critSet (r := r) hp κ c B z) :
    ∃ (j : Fin (p + q + 1)) (v : Fin (FQ (p + q) p) → ℝ),
      critFibreCond (p := p) hp κ (Pof c B κ) (Gsof c B κ) j (Fin.append (gpBP c z) v) ∧
      projU (p + q) p v = u := by
  obtain ⟨j, pnt, hz, hh, hu, hc, _⟩ :=
    critCond_imp_exists_witness (hp := hp) (κ := κ) (hκ := hκ) (P := Pof c B κ)
      (Gs := Gsof c B κ) (z := z) (h := hvec c z) (u := u) h
  refine ⟨j, fun y => pnt (Fin.natAdd (BP (p + q) r) y), ?_, ?_⟩
  · have hEq : Fin.append (gpBP c z) (fun y => pnt (Fin.natAdd (BP (p + q) r) y)) = pnt := by
      funext i
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left]
        induction i using Fin.addCases with
        | left i' =>
          rw [gpBP_castAdd]
          exact ((congrArg pnt (show (Fin.castAdd (FQ (p + q) p) (Fin.castAdd r i')
            : Fin (BP (p + q) r + FQ (p + q) p)) = idxZ (p + q) r p i' from Fin.ext rfl)).trans
            (hz i')).symm
        | right j' =>
          rw [gpBP_natAdd]
          exact ((congrArg pnt (show (Fin.castAdd (FQ (p + q) p) (Fin.natAdd (p + q) j')
            : Fin (BP (p + q) r + FQ (p + q) p)) = idxH (p + q) r p j' from Fin.ext rfl)).trans
            (hh j')).symm
      | right y => rw [Fin.append_right]
    rw [hEq]; exact hc
  · funext i
    show pnt (Fin.natAdd (BP (p + q) r) (fU (p + q) p i)) = u i
    have h' := hu i
    rw [idxU_eq_natAdd] at h'
    exact h'

theorem cloU_iff_cloV (hp : p ≤ p + q) {κ : ℕ} (hκ : 1 ≤ κ) (c : EAChain (p + q) r)
    (B : Basic (p + q) r) (z : Fin (p + q) → ℝ) :
    (0 : Fin (FQ (p + q) p) → ℝ) ∈ closure (uSet (r := r) hp κ c B z) ↔
      (0 : Fin (p + q) → ℝ) ∈ closure (critSet (r := r) hp κ c B z) := by
  constructor
  · intro h0
    have h1 : projU (p + q) p 0 ∈ closure (projU (p + q) p '' uSet (r := r) hp κ c B z) :=
      image_closure_subset_closure_image (continuous_projU (p + q) p) ⟨0, h0, rfl⟩
    simp only [projU_zero] at h1
    refine closure_mono ?_ h1
    rintro u ⟨v, ⟨j, hj⟩, rfl⟩
    have hh : ∀ j' : Fin r, (Fin.append (gpBP c z) v) (idxH (p + q) r p j') = hvec c z j' :=
      fun j' => appPt_idxH c z v j'
    have hc := critFibreCond_imp_critCond (hp := hp) (κ := κ) (hκ := hκ) (P := Pof c B κ)
      (Gs := Gsof c B κ) (h := hvec c z) (pnt := Fin.append (gpBP c z) v) hh j hj
    have hz : (fun i => (Fin.append (gpBP c z) v) (idxZ (p + q) r p i)) = z := by
      funext i; exact appPt_idxZ c z v i
    have hu : (fun i => (Fin.append (gpBP c z) v) (idxU (p + q) r p i)) =
        projU (p + q) p v := by
      funext i; exact appPt_idxU c z v i
    rwa [hz, hu] at hc
  · intro h0
    rw [Metric.mem_closure_iff] at h0 ⊢
    intro ε hε
    have hδ : 0 < min 1 (ε ^ 2 / 2) := lt_min one_pos (by positivity)
    obtain ⟨u, hu, huε⟩ := h0 (min 1 (ε ^ 2 / 2)) hδ
    have hu1 : dist u 0 ≤ 1 := by
      have h := lt_of_lt_of_le huε (min_le_left 1 (ε ^ 2 / 2))
      rw [dist_comm] at h
      exact h.le
    obtain ⟨j, v, hv, huv⟩ := critCond_witness (r := r) hp hκ c B z u hu
    refine ⟨v, ⟨j, hv⟩, ?_⟩
    have hb := critFibreCond_bound (hp := hp) (κ := κ) (hκ := hκ) (P := Pof c B κ)
      (Gs := Gsof c B κ) (c := c) (z := z) (v := v) (j := j) hv (by rw [huv]; exact hu1)
    rw [huv] at hb
    have h2u : 2 * dist u 0 < ε ^ 2 := by
      have h := lt_of_lt_of_le huε (min_le_right 1 (ε ^ 2 / 2))
      rw [dist_comm] at h
      linarith
    have hs : Real.sqrt (2 * dist u 0) < ε := by
      calc Real.sqrt (2 * dist u 0) < Real.sqrt (ε ^ 2) :=
            Real.sqrt_lt_sqrt (by positivity) h2u
        _ = ε := Real.sqrt_sq hε.le
    rw [dist_comm]
    linarith

/-! ## §4. The union over the basic sets -/

/-- The union of a list of sets. -/
def listUnion {α : Type*} (l : List (Set α)) : Set α := l.foldr (· ∪ ·) ∅

theorem mem_listUnion {α : Type*} {l : List (Set α)} {x : α} :
    x ∈ listUnion l ↔ ∃ s ∈ l, x ∈ s := by
  induction l with
  | nil => simp [listUnion]
  | cons a t ih =>
      rw [show listUnion (a :: t) = a ∪ listUnion t from rfl]
      simp only [Set.mem_union, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨s, hs, hx⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨s, Or.inr hs, hx⟩
      · rintro ⟨s, hs | hs, hx⟩
        · exact Or.inl (hs ▸ hx)
        · exact Or.inr ⟨s, hs, hx⟩

theorem closure_listUnion {α : Type*} [TopologicalSpace α] (l : List (Set α)) :
    closure (listUnion l) = listUnion (l.map closure) := by
  induction l with
  | nil => simp [listUnion]
  | cons a t ih =>
      rw [show listUnion (a :: t) = a ∪ listUnion t from rfl, closure_union,
        show (a :: t).map closure = closure a :: t.map closure from rfl,
        show listUnion (closure a :: t.map closure) = closure a ∪ listUnion (t.map closure)
          from rfl, ih]

/-- Membership in the union of the criterion pieces of `X`. -/
theorem mem_critUnion_set (hp : p ≤ p + q) (κ : ℕ) (X : SemiPf (p + q))
    (pt : Fin (BP (p + q) X.r + FQ (p + q) p) → ℝ) :
    pt ∈ (critUnion (p := p) hp κ X).set ↔
      ∃ B ∈ X.basics, ∃ j : Fin (p + q + 1),
        critFibreCond (p := p) hp κ (Pof X.c B κ) (Gsof X.c B κ) j pt := by
  rw [critUnion, SA.set]
  constructor
  · rintro ⟨B', hB', hh⟩
    rw [List.mem_flatMap] at hB'
    obtain ⟨B, hB, hB'⟩ := hB'
    rw [List.mem_map] at hB'
    obtain ⟨j, -, rfl⟩ := hB'
    exact ⟨B, hB, j,
      (critBasic_holds_iff (p := p) hp κ (Pof X.c B κ) (Gsof X.c B κ) j pt).mp hh⟩
  · rintro ⟨B, hB, j, hj⟩
    refine ⟨critBasic (p := p) hp κ (Pof X.c B κ) (Gsof X.c B κ) j, ?_, ?_⟩
    · rw [List.mem_flatMap]
      exact ⟨B, hB, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩
    · exact (critBasic_holds_iff (p := p) hp κ (Pof X.c B κ) (Gsof X.c B κ) j pt).mpr hj

/-- The fibre of the union of the criterion pieces, over `z`, is the union over the basic sets
of the witness sets. -/
theorem fiber_critUnion_eq (hp : p ≤ p + q) (κ : ℕ) (X : SemiPf (p + q))
    (z : Fin (p + q) → ℝ) :
    fiber (critUnion (p := p) hp κ X).set (gpBP X.c z)
      = listUnion (X.basics.map (fun B => uSet (r := X.r) hp κ X.c B z)) := by
  ext v
  rw [mem_listUnion]
  change (Fin.append (gpBP X.c z) v ∈ (critUnion (p := p) hp κ X).set) ↔
    (∃ S ∈ X.basics.map (fun B => uSet (r := X.r) hp κ X.c B z), v ∈ S)
  constructor
  · intro hv
    obtain ⟨B, hB, j, hj⟩ := (mem_critUnion_set (p := p) hp κ X _).mp hv
    exact ⟨uSet (r := X.r) hp κ X.c B z, List.mem_map.mpr ⟨B, hB, rfl⟩, j, hj⟩
  · rintro ⟨S, hS, hv⟩
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hS
    obtain ⟨j, hj⟩ := hv
    exact (mem_critUnion_set (p := p) hp κ X _).mpr ⟨B, hB, j, hj⟩

/-! ## §5. The fibre of `X.set` as the union of the fibres of the basic sets -/

/-- `Fin.append (projFirst p q z) (projSnd p q z) = z`. -/
theorem fin_append_projFirst_projSnd (p q : ℕ) (z : Fin (p + q) → ℝ) :
    Fin.append (projFirst p q z) (projSnd p q z) = z := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [projFirst, Fin.append_left]
  | right j => simp [projSnd, Fin.append_right]

/-- `projFirst p q (Fin.append x y) = x`. -/
theorem projFirst_append (p q : ℕ) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    projFirst p q (Fin.append x y) = x := by
  funext i; simp [projFirst, Fin.append_left]

/-- Cube saturation makes the fibre of `X.set` the union of the fibres of the basic sets. -/
theorem fiber_set_eq (X : SemiPf (p + q))
    (hsat : ∀ B ∈ X.basics, ∀ z : Fin (p + q) → ℝ, B.holds X.c z → z ∈ cubeC (p + q))
    (x : Fin p → ℝ) :
    fiber X.set x = listUnion (X.basics.map (fun B => fiber (B.holds X.c) x)) := by
  ext y
  rw [mem_listUnion]
  change (Fin.append x y ∈ X.set) ↔
    (∃ S ∈ X.basics.map (fun B => fiber (B.holds X.c) x), y ∈ S)
  constructor
  · rintro ⟨-, B, hB, hBh⟩
    exact ⟨fiber (B.holds X.c) x, List.mem_map.mpr ⟨B, hB, rfl⟩, hBh⟩
  · rintro ⟨S, hS, hyS⟩
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hS
    exact ⟨hsat B hB (Fin.append x y) hyS, B, hB, hyS⟩

/-- The base of the fibre closure: the closure of the fibre at `z` is computed by the frozen
basic set (E3b). -/
theorem perB_closure_iff_critSet (K : Polynomial ℕ) (F : ℕ)
    (hK : ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r) (y : Fin k → ℝ) (κ : ℕ),
      k + r ≤ F → K.eval B.deg < κ →
      (y ∈ closure {x | B.holds c x} ↔
        y ∈ closure {x | (∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)) ∧
          (∀ g ∈ B.pos, dist x y ^ κ < eaTaylor c g κ y x)}))
    (hp : p ≤ p + q) {κ : ℕ} (hκ : 1 ≤ κ) (c : EAChain (p + q) r) (B : Basic (p + q) r)
    (z : Fin (p + q) → ℝ) (hfmt : (p + q) + r ≤ F)
    (hdeg : K.eval (frozenBasic p q r B z).deg < κ) :
    projSnd p q z ∈ closure (fiber (B.holds c) (projFirst p q z)) ↔
      (0 : Fin (p + q) → ℝ) ∈ closure (critSet (r := r) hp κ c B z) := by
  have hfib : (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) ''
        fiber (B.holds c) (projFirst p q z)
      = {z' : Fin (p + q) → ℝ | B.holds c z' ∧ projFirst p q z' = projFirst p q z} := by
    ext z'
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, projFirst_append p q (projFirst p q z) y⟩
    · rintro ⟨hz', hpf⟩
      refine ⟨projSnd p q z', ?_, ?_⟩
      · show B.holds c (Fin.append (projFirst p q z) (projSnd p q z'))
        rw [← hpf, fin_append_projFirst_projSnd p q z']
        exact hz'
      · rw [← hpf]
        exact fin_append_projFirst_projSnd p q z'
  have h1 : projSnd p q z ∈ closure (fiber (B.holds c) (projFirst p q z))
      ↔ z ∈ closure {z' : Fin (p + q) → ℝ | (frozenBasic p q r B z).holds c z'} := by
    have hset : {z' : Fin (p + q) → ℝ | B.holds c z' ∧ projFirst p q z' = projFirst p q z}
        = {z' : Fin (p + q) → ℝ | (frozenBasic p q r B z).holds c z'} := by
      ext z'
      exact (frozenBasic_holds_iff c B z z').symm
    rw [mem_closure_append_iff, hfib, fin_append_projFirst_projSnd, hset]
  rw [h1, hK (p + q) r c (frozenBasic p q r B z) z κ hfmt hdeg]
  have hset2 : {x : Fin (p + q) → ℝ |
        (∀ f ∈ (frozenBasic p q r B z).eqs,
          |eaTaylor c f (κ ^ 2) z x| ≤ dist x z ^ (κ ^ 2)) ∧
        (∀ g ∈ (frozenBasic p q r B z).pos, dist x z ^ κ < eaTaylor c g κ z x)}
      = (fun u : Fin (p + q) → ℝ => z + u) '' critSet (r := r) hp κ c B z := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hx
      refine ⟨x - z, ?_, ?_⟩
      · refine (frozen_crit_iff (p := p) (q := q) (r := r) hp hκ c B z (x - z)).mp ?_
        have hzx : z + (x - z) = x := by
          funext i; simp [Pi.add_apply, Pi.sub_apply]
        rwa [hzx]
      · funext i; simp [Pi.add_apply, Pi.sub_apply]
    · rintro ⟨u, hu, rfl⟩
      exact (frozen_crit_iff (p := p) (q := q) (r := r) hp hκ c B z u).mpr hu
  rw [hset2]
  exact mem_closure_translate (p + q) z (critSet (r := r) hp κ c B z)

/-- The per-basic-set fibre closure equivalence. -/
theorem perB_iff (K : Polynomial ℕ) (F : ℕ)
    (hK : ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r) (y : Fin k → ℝ) (κ : ℕ),
      k + r ≤ F → K.eval B.deg < κ →
      (y ∈ closure {x | B.holds c x} ↔
        y ∈ closure {x | (∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)) ∧
          (∀ g ∈ B.pos, dist x y ^ κ < eaTaylor c g κ y x)}))
    (hp : p ≤ p + q) (X : SemiPf (p + q)) (B : Basic (p + q) X.r) (z : Fin (p + q) → ℝ)
    (hfmt : (p + q) + X.r ≤ F)
    (hdeg : K.eval (frozenBasic p q X.r B z).deg < kappa K X.deg p) :
    (0 : Fin (FQ (p + q) p) → ℝ) ∈
        closure (uSet (r := X.r) hp (kappa K X.deg p) X.c B z) ↔
      projSnd p q z ∈ closure (fiber (B.holds X.c) (projFirst p q z)) :=
  (cloU_iff_cloV hp (by rw [kappa]; omega) X.c B z).trans
    (perB_closure_iff_critSet K F hK hp (by rw [kappa]; omega) X.c B z hfmt hdeg).symm


/-- Membership in `fiberClosure`. -/
theorem mem_fiberClosure_iff {p q : ℕ} {S : Set (Fin (p + q) → ℝ)} {P : Fin (p + q) → ℝ} :
    P ∈ fiberClosure S ↔ projSnd p q P ∈ closure (fiber S (projFirst p q P)) := Iff.rfl

/-- `projSnd p q (Fin.append x y) = y`. -/
theorem projSnd_append (p q : ℕ) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    projSnd p q (Fin.append x y) = y := by
  funext j; simp [projSnd, Fin.append_right]

/-- Degree of a member of a list of basic sets. -/
theorem deg_le_sum {k r : ℕ} {l : List (Basic k r)} {B : Basic k r} (h : B ∈ l) :
    B.deg ≤ (l.map Basic.deg).sum := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      rcases List.mem_cons.mp h with rfl | h
      · simp only [List.map_cons, List.sum_cons]; omega
      · have := ih h
        simp only [List.map_cons, List.sum_cons]; omega

/-- The total degree of `eval₂Hom` with variables of degree `≤ 1`. -/
theorem totalDegree_eval₂Hom_le {σ τ : Type*} (g : σ → MvPolynomial τ ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (Q : MvPolynomial σ ℝ) :
    (MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial τ ℝ) g Q).totalDegree ≤
      Q.totalDegree := by
  change (Q.eval₂ (MvPolynomial.C : ℝ →+* MvPolynomial τ ℝ) g).totalDegree ≤ Q.totalDegree
  rw [MvPolynomial.eval₂_eq]
  refine MvPolynomial.totalDegree_finsetSum_le (fun d hd => ?_)
  calc (MvPolynomial.C (Q.coeff d) * ∏ i ∈ d.support, g i ^ d i).totalDegree
      ≤ (MvPolynomial.C (Q.coeff d)).totalDegree +
          (∏ i ∈ d.support, g i ^ d i).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (∏ i ∈ d.support, g i ^ d i).totalDegree := by
        rw [MvPolynomial.totalDegree_C, Nat.zero_add]
    _ ≤ ∑ i ∈ d.support, (g i ^ d i).totalDegree :=
        MvPolynomial.totalDegree_finsetProd d.support (fun i => g i ^ d i)
    _ ≤ ∑ i ∈ d.support, d i := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        calc (g i ^ d i).totalDegree ≤ d i * (g i).totalDegree := MvPolynomial.totalDegree_pow _ _
          _ ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
          _ = d i := mul_one _
    _ ≤ Q.totalDegree := by
        have := MvPolynomial.le_totalDegree (p := Q) hd
        simpa [Finsupp.sum] using this

/-- Slicing does not increase the degree. -/
theorem totalDegree_sliceHom_le {m n : ℕ} (Q : EAPoly (m + n) 0) :
    (sliceHom m n Q).totalDegree ≤ Q.totalDegree := by
  rw [sliceHom, saPoly_eq_rename]
  refine (MvPolynomial.totalDegree_rename_le _ _).trans ?_
  refine (totalDegree_eval₂Hom_le (fun i => sliceMap m n i) ?_ (saUnpoly (m + n) Q)).trans ?_
  · intro i
    unfold sliceMap
    split_ifs with h
    · rw [MvPolynomial.totalDegree_X]
    · simp
  · rw [saUnpoly]
    exact MvPolynomial.totalDegree_rename_le _ _

/-- The slice of an `SA`-set has degree at most the degree of the set. -/
theorem saSlice_deg_le (m n : ℕ) (X : SA (m + n)) : (saSlice m n X).deg ≤ X.deg := by
  have h : ∀ Q : EAPoly (m + n) 0, atomDeg (sliceHom m n Q) ≤ atomDeg Q := by
    intro Q
    simp only [atomDeg]
    exact Nat.add_le_add_right (totalDegree_sliceHom_le Q) 1
  show ((X.basics.map (fun B => (⟨B.eqs.map (sliceHom m n), B.pos.map (sliceHom m n)⟩ :
      Basic m 0))).map Basic.deg).sum ≤ (X.basics.map Basic.deg).sum
  rw [List.map_map]
  refine List.sum_le_sum (fun B _ => ?_)
  simp only [Function.comp_apply, Basic.deg, List.map_append, List.sum_append, List.map_map]
  exact Nat.add_le_add
    (List.sum_le_sum (fun Q _ => by simpa only [Function.comp_apply] using h Q))
    (List.sum_le_sum (fun Q _ => by simpa only [Function.comp_apply] using h Q))

/-- Under cube saturation, every basic set has degree at least `1` (it has an atom). -/
theorem one_le_deg_of_cubesat {k : ℕ} (hk : 0 < k) {X : SemiPf k}
    (hsat : ∀ B ∈ X.basics, ∀ z : Fin k → ℝ, B.holds X.c z → z ∈ cubeC k)
    {B : Basic k X.r} (hB : B ∈ X.basics) : 1 ≤ B.deg := by
  by_contra hlt
  have hdeg0 : B.deg = 0 := by omega
  have hsum : ((B.eqs ++ B.pos).map atomDeg).sum = 0 := by
    simpa only [Basic.deg] using hdeg0
  have hnil : B.eqs ++ B.pos = [] := by
    by_contra hne
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
    have hle : atomDeg a ≤ ((B.eqs ++ B.pos).map atomDeg).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)
    have h1 : 1 ≤ atomDeg a := by simp only [atomDeg]; omega
    omega
  obtain ⟨heqs, hpos⟩ := List.append_eq_nil_iff.mp hnil
  let z : Fin k → ℝ := fun i => if i = ⟨0, hk⟩ then 2 else 0
  have hholds : B.holds X.c z := by
    rw [Basic.holds, heqs, hpos]
    simp
  have hcube := hsat B hB z hholds
  have h2 : |z ⟨0, hk⟩| ≤ 1 := hcube ⟨0, hk⟩
  have hz2 : z ⟨0, hk⟩ = 2 := by simp [z]
  rw [hz2] at h2
  norm_num at h2

/-- In dimension `0`, the fibrewise closure is the set itself. -/
theorem fiberClosure_zero (X : SemiPf 0) :
    fiberClosure (p := 0) (q := 0) X.set = X.set := by
  classical
  ext z
  change projSnd 0 0 z ∈ closure (fiber (p := 0) (q := 0) X.set (projFirst 0 0 z)) ↔
    z ∈ X.set
  have hz : projSnd 0 0 z = z := by funext i; exact i.elim0
  rw [hz]
  have hfib : fiber (p := 0) (q := 0) X.set (projFirst 0 0 z) =
      (if z ∈ X.set then Set.univ else ∅) := by
    by_cases h : z ∈ X.set
    · ext y
      simp only [h, if_pos, Set.mem_univ, iff_true]
      show Fin.append (projFirst 0 0 z) y ∈ X.set
      have happ : Fin.append (projFirst 0 0 z) y = z := by funext i; exact i.elim0
      rw [happ]
      exact h
    · ext y
      simp only [h, if_neg, not_false_eq_true, Set.mem_empty_iff_false, iff_false]
      show ¬ Fin.append (projFirst 0 0 z) y ∈ X.set
      have happ : Fin.append (projFirst 0 0 z) y = z := by funext i; exact i.elim0
      rw [happ]
      exact h
  rw [hfib]
  by_cases h : z ∈ X.set <;> simp [h]

end Assembly

end Work.WilE6
