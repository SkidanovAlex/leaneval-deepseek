/-
  WilC4/IntDomFam_definable : `IntDomFam Y` is `∅`-definable whenever `Y` is.

  `IntDomFam Y ⊆ ℝ^{k+1}` is the family of points `v = (x, c)` at which the fibre of `Y` over the
  parameter tuple `c` is defined on a *neighbourhood* of `x`:

      v ∈ IntDomFam Y ↔ ∃ δ > 0, ∀ t, x - δ < t < x + δ → ∃ w, (t, w, c) ∈ Y.

  The only content is the quantifier bookkeeping.  The relation `(t,w,c) ∈ Y` is the preimage of
  `Y` under the reindexing reading `(t,w,c)` off the slots `sl_t`, `sl_w`, `sl_v` of the context
  `(v,δ,t,w)`; the "invalid" set `Aint` (`v 0 < t + δ ∧ t < v 0 + δ`, i.e. `x - δ < t < x + δ`)
  is built from the elementary additive atoms of `crit_def_bad_aux`; and the alternating `∃δ∀t∃w`
  block is handled by `exists_of_finite` / `forall_of_finite`.
-/
import Mathlib
import Submission.Work.WilC4.crit_def_bad_aux
import Submission.Work.WilC4.CritDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

variable {k : ℕ}

/-! ## 1. The variable contexts `(v,δ)`, `(v,δ,t)`, `(v,δ,t,w)` and the slot maps -/

/-- The variable context `(v, δ)`: the parameter tuple `v : ℝ^{k+1}` and the radius `δ`. -/
abbrev IdD1 (k : ℕ) := Fin (k + 1) ⊕ Fin 1

/-- The variable context `(v, δ, t)`. -/
abbrev IdD2 (k : ℕ) := (Fin (k + 1) ⊕ Fin 1) ⊕ Fin 1

/-- The variable context `(v, δ, t, w)`. -/
abbrev IdD3 (k : ℕ) := ((Fin (k + 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1

/-- The slot of the parameter `v i` inside the context `(v,δ,t,w)`. -/
def sl_v {k : ℕ} (i : Fin (k + 1)) : IdD3 k := Sum.inl (Sum.inl (Sum.inl i))

/-- The slot of `δ`. -/
def sl_d {k : ℕ} : IdD3 k := Sum.inl (Sum.inl (Sum.inr 0))

/-- The slot of `t`. -/
def sl_t {k : ℕ} : IdD3 k := Sum.inl (Sum.inr 0)

/-- The slot of `w`. -/
def sl_w {k : ℕ} : IdD3 k := Sum.inr 0

/-! ## 2. The relation `(t,w,c) ∈ Y` in the context `(v,δ,t,w)` -/

/-- The graph of `Y` read in the context `(v,δ,t,w)`: the argument `t` is the second coordinate,
the value `w` the first, and the parameter tail is the `v`-block.  Concretely
`u ∈ Ysub Y ↔ (u sl_t, u sl_w, tup (u ∘ sl_v)) ∈ Y`. -/
def Ysub (Y : Set (Fin (k + 2) → ℝ)) : Set (IdD3 k → ℝ) :=
  GrSub Y (fun j => sl_v j) sl_t sl_w

lemma mem_Ysub_iff {Y : Set (Fin (k + 2) → ℝ)} (u : IdD3 k → ℝ) :
    u ∈ Ysub Y ↔ CGr Y (tup (fun j => u (sl_v j))) (u sl_t) (u sl_w) :=
  Iff.rfl

theorem Ysub_definable {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (Ysub Y) :=
  GrSub_definable hY (fun j => sl_v j) sl_t sl_w

/-! ## 3. The "invalid interval" set and the implication `Aint → Ysub` -/

/-- The condition `v 0 - δ < t` is `v 0 < t + δ`; the second conjunct is `t < v 0 + δ`. -/
def Aint (k : ℕ) : Set (IdD3 k → ℝ) :=
  {u | u (sl_v 0) < u sl_t + u sl_d ∧ u sl_t < u (sl_v 0) + u sl_d}

theorem Aint_definable (k : ℕ) : (∅ : Set ℝ).Definable LRc (Aint k) := by
  have h1 := definable_lt_add (ρ := IdD3 k) (sl_v (0 : Fin (k + 1))) sl_t sl_d
  have h2 := definable_lt_add (ρ := IdD3 k) sl_t (sl_v (0 : Fin (k + 1))) sl_d
  have h := h1.inter h2
  convert h using 1
  ext u
  simp only [Aint, Set.mem_ofPred_eq, Set.mem_inter_iff]

/-- The set of `u = (v,δ,t,w)` such that either the interval condition fails or `(t,w,c) ∈ Y`:
the inner implication `Aint → Ysub`. -/
def Psi (Y : Set (Fin (k + 2) → ℝ)) : Set (IdD3 k → ℝ) :=
  {u | u ∈ Aint k → u ∈ Ysub Y}

theorem Psi_definable {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (Psi Y) := by
  have hA : (∅ : Set ℝ).Definable LRc (Aint k) := Aint_definable k
  have h := hA.compl.union (Ysub_definable hY)
  convert h using 1
  ext u
  simp only [Psi, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
  tauto

/-! ## 4. Eliminating `w`, then `t`, then adding `0 < δ`, then eliminating `δ` -/

/-- Eliminate `w`. -/
def Psi2 (Y : Set (Fin (k + 2) → ℝ)) : Set (IdD2 k → ℝ) :=
  {z | ∃ w : Fin 1 → ℝ, Sum.elim z w ∈ Psi Y}

theorem Psi2_definable {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (Psi2 Y) := by
  have h := (Psi_definable hY).exists_of_finite (α := IdD2 k) (β := Fin 1)
  convert h using 1
  ext z
  simp only [Psi2, Set.mem_ofPred_eq]

/-- Eliminate `t` (universally). -/
def Psi3 (Y : Set (Fin (k + 2) → ℝ)) : Set (IdD1 k → ℝ) :=
  {z | ∀ t : Fin 1 → ℝ, Sum.elim z t ∈ Psi2 Y}

theorem Psi3_definable {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (Psi3 Y) := by
  have h := (Psi2_definable hY).forall_of_finite (α := IdD1 k) (β := Fin 1)
  convert h using 1
  ext z
  simp only [Psi3, Set.mem_ofPred_eq]

/-- Add the condition `0 < δ`. -/
def Psi4 (Y : Set (Fin (k + 2) → ℝ)) : Set (IdD1 k → ℝ) :=
  Psi3 Y ∩ {z | 0 < z (Sum.inr (0 : Fin 1))}

theorem Psi4_definable {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (Psi4 Y) := by
  have h0 : (∅ : Set ℝ).Definable LRc {z : IdD1 k → ℝ | 0 < z (Sum.inr (0 : Fin 1))} :=
    definable_lt_const (0 : ℝ) (Sum.inr (0 : Fin 1))
  exact (Psi3_definable hY).inter h0

/-- Eliminate `δ`. -/
def E (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | ∃ δ : Fin 1 → ℝ, Sum.elim v δ ∈ Psi4 Y}

theorem E_definable {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (E Y) := by
  have h := (Psi4_definable hY).exists_of_finite (α := Fin (k + 1)) (β := Fin 1)
  convert h using 1
  ext v
  simp only [E, Set.mem_ofPred_eq]

/-! ## 5. `E Y` is exactly `IntDomFam Y` -/

/-- Unfolding of `E`: a pointwise description. -/
lemma mem_E_iff {Y : Set (Fin (k + 2) → ℝ)} (v : Fin (k + 1) → ℝ) :
    v ∈ E Y ↔ ∃ δ : Fin 1 → ℝ, 0 < δ 0 ∧ ∀ t : Fin 1 → ℝ, ∃ w : Fin 1 → ℝ,
      ((v 0 < t 0 + δ 0 ∧ t 0 < v 0 + δ 0) → CGr Y (tup v) (t 0) (w 0)) := by
  simp only [E, Set.mem_ofPred_eq, Psi4, Psi3, Psi2, Psi, Aint, Ysub, GrSub, CGr,
    Set.mem_inter_iff, Sum.elim_inr]
  exact exists_congr (fun δ => and_comm)

/-- The `Fin 1`-form of `IntDom`. -/
lemma intdom_iff_form {Y : Set (Fin (k + 2) → ℝ)} (v : Fin (k + 1) → ℝ) :
    IntDom Y (tup v) (v 0) ↔
      ∃ δ : Fin 1 → ℝ, 0 < δ 0 ∧ ∀ t : Fin 1 → ℝ, ∃ w : Fin 1 → ℝ,
        ((v 0 < t 0 + δ 0 ∧ t 0 < v 0 + δ 0) → CGr Y (tup v) (t 0) (w 0)) := by
  rw [IntDom]
  constructor
  · rintro ⟨δ₀, hδ, H⟩
    refine ⟨fun _ => δ₀, by simpa using hδ, fun t => ?_⟩
    by_cases hA : v 0 < t 0 + δ₀ ∧ t 0 < v 0 + δ₀
    · obtain ⟨h1, h2⟩ := hA
      obtain ⟨w, hw⟩ := H (t 0) (by rw [sub_lt_iff_lt_add]; exact h1) h2
      exact ⟨fun _ => w, fun _ => hw⟩
    · exact ⟨fun _ => 0, fun h => absurd h hA⟩
  · rintro ⟨δ, hδ, H⟩
    refine ⟨δ 0, by simpa using hδ, ?_⟩
    intro t ht1 ht2
    have h1 : v 0 < t + δ 0 := by rw [sub_lt_iff_lt_add] at ht1; exact ht1
    obtain ⟨w, hw⟩ := H (fun _ : Fin 1 => t)
    exact ⟨w 0, hw ⟨h1, ht2⟩⟩

theorem IntDomFam_eq_E (Y : Set (Fin (k + 2) → ℝ)) : IntDomFam Y = E Y := by
  ext v
  show IntDom Y (tup v) (v 0) ↔ v ∈ E Y
  rw [intdom_iff_form v, mem_E_iff v]

/-! ## 6. The theorem -/

theorem IntDomFam_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.IntDomFam Y) := by
  rw [IntDomFam_eq_E Y]
  exact E_definable hY

end Work.WilC4
