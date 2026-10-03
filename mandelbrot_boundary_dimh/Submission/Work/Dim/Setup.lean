import Mathlib
import Submission.Work.Interfaces.Basic

/-!
# Conformal IFS: basic setup (area DIM)

Definitions and elementary structural lemmas for the dimension lower bound of the limit set of a
conformal IFS `τ : Fin N → ℂ → ℂ` on the ball `ball p r` (area DIM of the project).

* `pref ω k` : the list of the first `k` letters of the infinite word `ω`
  (`codingPt τ p ω = lim_k (ifsComp τ (pref ω k)) p`).
* `piece τ p r w` : the image of `closedBall p (r/2)` under `ifsComp τ w`; the limit set is the
  nested intersection of the pieces along a code.
* `asize τ p w` : `‖deriv (ifsComp τ w) p‖`, the "size" of the piece used for the Moran cover.
-/

open MandelDim
open scoped Topology MeasureTheory ENNReal
open Set Metric Filter Function

noncomputable section

namespace Work.Dim

variable {N : ℕ}

/-- The prefix of length `k` of an infinite word, as a list. -/
def pref (ω : ℕ → Fin N) (k : ℕ) : List (Fin N) := (List.range k).map ω

@[simp] theorem pref_length (ω : ℕ → Fin N) (k : ℕ) : (pref ω k).length = k := by
  simp [pref]

@[simp] theorem pref_zero (ω : ℕ → Fin N) : pref ω 0 = [] := by simp [pref]

theorem pref_succ (ω : ℕ → Fin N) (k : ℕ) : pref ω (k + 1) = pref ω k ++ [ω k] := by
  simp [pref, List.range_succ]

/-- The piece of the limit set associated with a finite word. -/
def piece (τ : Fin N → ℂ → ℂ) (p : ℂ) (r : ℝ) (w : List (Fin N)) : Set ℂ :=
  ifsComp τ w '' closedBall p (r / 2)

/-- The size of a word: the modulus of the derivative of the composition at the base point. -/
def asize (τ : Fin N → ℂ → ℂ) (p : ℂ) (w : List (Fin N)) : ℝ := ‖deriv (ifsComp τ w) p‖

/-! ### Composition of the branches -/

theorem ifsComp_append {τ : Fin N → ℂ → ℂ} (w v : List (Fin N)) :
    ifsComp τ (w ++ v) = ifsComp τ w ∘ ifsComp τ v := by
  induction w with
  | nil => simp [ifsComp]
  | cons i w ih => simp [ifsComp, ih, Function.comp_assoc]

theorem ifsComp_append_singleton {τ : Fin N → ℂ → ℂ} (w : List (Fin N)) (i : Fin N) :
    ifsComp τ (w ++ [i]) = ifsComp τ w ∘ τ i := by
  induction w with
  | nil => simp [ifsComp]
  | cons j w ih => simp [ifsComp, ih, Function.comp_assoc]

/-- Every nonempty composition maps `ball p r` into `ball p (r/2)`. -/
theorem ifsComp_mapsTo {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hτ : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ w : List (Fin N), w ≠ [] → MapsTo (ifsComp τ w) (ball p r) (ball p (r / 2)) := by
  intro w
  induction w with
  | nil => intro h; exact absurd rfl h
  | cons i w ih =>
      intro _
      cases w with
      | nil => simpa [ifsComp] using hτ i
      | cons j v =>
          have h1 : MapsTo (ifsComp τ (j :: v)) (ball p r) (ball p (r / 2)) :=
            ih (List.cons_ne_nil j v)
          have h1' : MapsTo (ifsComp τ (j :: v)) (ball p r) (ball p r) := by
            intro z hz
            have hz' := h1 hz
            rw [mem_ball] at hz' ⊢
            linarith [hz', hr]
          exact (hτ i).comp h1'

/-- Every nonempty composition is injective on `ball p r`. -/
theorem ifsComp_injOn {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hτ : ∀ i, InjOn (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ w : List (Fin N), w ≠ [] → InjOn (ifsComp τ w) (ball p r) := by
  intro w
  induction w with
  | nil => intro h; exact absurd rfl h
  | cons i w ih =>
      intro _
      cases w with
      | nil => simpa [ifsComp] using hτ i
      | cons j v =>
          have h1 : InjOn (ifsComp τ (j :: v)) (ball p r) := ih (List.cons_ne_nil j v)
          have hm : MapsTo (ifsComp τ (j :: v)) (ball p r) (ball p r) :=
            (ifsComp_mapsTo hr hmaps _ (by simp)).mono_right (by
              intro z hz
              rw [mem_ball] at hz ⊢
              linarith [hz, hr])
          have := (hτ i).comp h1 hm
          simpa [ifsComp] using this

/-- Every nonempty composition maps `closedBall p (r/2)` into itself. -/
theorem ifsComp_mapsTo_closedBall {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hτ : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ w : List (Fin N), w ≠ [] →
      MapsTo (ifsComp τ w) (closedBall p (r / 2)) (closedBall p (r / 2)) := by
  intro w hw z hz
  have hzr : z ∈ ball p r := by
    rw [mem_closedBall] at hz; rw [mem_ball]; linarith [hz, hr]
  have := (ifsComp_mapsTo hr hτ w hw) hzr
  rw [mem_ball] at this; rw [mem_closedBall]; exact le_of_lt this

/-- Analyticity of the compositions at points of `ball p r`. -/
theorem ifsComp_analyticAt {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ w : List (Fin N), w ≠ [] → ∀ z ∈ ball p r, AnalyticAt ℂ (ifsComp τ w) z := by
  intro w
  induction w with
  | nil => intro h; exact absurd rfl h
  | cons i w ih =>
      intro _ z hz
      cases w with
      | nil => simpa [ifsComp] using (hdiff i).analyticAt (isOpen_ball.mem_nhds hz)
      | cons j v =>
          have h1 : AnalyticAt ℂ (ifsComp τ (j :: v)) z := ih (List.cons_ne_nil j v) z hz
          have hm : ifsComp τ (j :: v) z ∈ ball p r := by
            have := (ifsComp_mapsTo hr hmaps (j :: v) (List.cons_ne_nil j v)) hz
            rw [mem_ball] at this ⊢
            linarith [this, hr]
          have h2 : AnalyticAt ℂ (τ i) (ifsComp τ (j :: v) z) :=
            (hdiff i).analyticAt (isOpen_ball.mem_nhds hm)
          simpa [ifsComp] using h2.comp h1

/-- Differentiability of the compositions at points of `ball p r`. -/
theorem ifsComp_differentiableAt {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ w : List (Fin N), w ≠ [] → ∀ z ∈ ball p r, DifferentiableAt ℂ (ifsComp τ w) z :=
  fun w hw z hz => (ifsComp_analyticAt hr hdiff hmaps w hw z hz).differentiableAt

/-- Chain rule for appending one letter at a general point. -/
theorem deriv_ifsComp_append_singleton {τ : Fin N → ℂ → ℂ} (w : List (Fin N))
    (i : Fin N) (z : ℂ) (h1 : DifferentiableAt ℂ (ifsComp τ w) (τ i z))
    (h2 : DifferentiableAt ℂ (τ i) z) :
    deriv (ifsComp τ (w ++ [i])) z = deriv (ifsComp τ w) (τ i z) * deriv (τ i) z := by
  rw [ifsComp_append_singleton, deriv_comp z h1 h2]

/-- Chain rule for prepending one letter. -/
theorem deriv_ifsComp_cons {τ : Fin N → ℂ → ℂ} (i : Fin N) (v : List (Fin N)) (z : ℂ)
    (h1 : DifferentiableAt ℂ (τ i) (ifsComp τ v z))
    (h2 : DifferentiableAt ℂ (ifsComp τ v) z) :
    deriv (ifsComp τ (i :: v)) z = deriv (τ i) (ifsComp τ v z) * deriv (ifsComp τ v) z := by
  rw [show ifsComp τ (i :: v) = τ i ∘ ifsComp τ v from rfl, deriv_comp z h1 h2]

/-- Lower bound for the derivative of a composition on the inner ball: if every branch has
derivative modulus at least `K⁻¹` on `ball p (r/2)`, so does every nonempty composition. -/
theorem le_norm_deriv_ifsComp {τ : Fin N → ℂ → ℂ} {p : ℂ} {r K : ℝ} (hr : 0 < r) (hK : 0 < K)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2)))
    (hlow : ∀ i, ∀ z ∈ ball p (r / 2), K⁻¹ ≤ ‖deriv (τ i) z‖) :
    ∀ w : List (Fin N), w ≠ [] → ∀ z ∈ ball p (r / 2),
      (K⁻¹) ^ w.length ≤ ‖deriv (ifsComp τ w) z‖ := by
  intro w
  induction w with
  | nil => intro h; exact absurd rfl h
  | cons i w ih =>
      intro hw z hz
      have hzr : z ∈ ball p r := by
        rw [mem_ball] at hz ⊢; linarith [hz, hr]
      cases w with
      | nil =>
          have hdt : DifferentiableAt ℂ (τ i) z :=
            (hdiff i).differentiableAt (isOpen_ball.mem_nhds hzr)
          have hid : DifferentiableAt ℂ (ifsComp τ ([] : List (Fin N))) z := by
            simp [ifsComp]
          have hchain := deriv_ifsComp_cons i ([] : List (Fin N)) z hdt hid
          have heq : deriv (ifsComp τ [i]) z = deriv (τ i) z := by
            rw [show ([i] : List (Fin N)) = i :: [] from rfl, hchain]
            simp [ifsComp]
          rw [List.length_cons, List.length_nil, pow_one, heq]
          exact hlow i z hz
      | cons j v =>
          have hmem : ifsComp τ (j :: v) z ∈ ball p (r / 2) :=
            ifsComp_mapsTo hr hmaps (j :: v) (List.cons_ne_nil j v) hzr
          have hmemr : ifsComp τ (j :: v) z ∈ ball p r := by
            rw [mem_ball] at hmem ⊢; linarith [hmem, hr]
          have hinner : DifferentiableAt ℂ (ifsComp τ (j :: v)) z :=
            ifsComp_differentiableAt hr hdiff hmaps (j :: v) (List.cons_ne_nil j v) z hzr
          have houter : DifferentiableAt ℂ (τ i) (ifsComp τ (j :: v) z) :=
            (hdiff i).differentiableAt (isOpen_ball.mem_nhds hmemr)
          have hchain := deriv_ifsComp_cons i (j :: v) z houter hinner
          have h1 : K⁻¹ ≤ ‖deriv (τ i) (ifsComp τ (j :: v) z)‖ := hlow i _ hmem
          have h2 := ih (List.cons_ne_nil j v) z hz
          have hKhalf : 0 < K⁻¹ := inv_pos.mpr hK
          calc (K⁻¹) ^ (i :: (j :: v)).length
              = K⁻¹ * (K⁻¹) ^ (j :: v).length := by
                rw [show (i :: (j :: v)).length = (j :: v).length + 1 from rfl, pow_succ]; ring
            _ ≤ ‖deriv (τ i) (ifsComp τ (j :: v) z)‖ * ‖deriv (ifsComp τ (j :: v)) z‖ :=
                mul_le_mul h1 h2 (pow_nonneg hKhalf.le _) (norm_nonneg _)
            _ = ‖deriv (ifsComp τ (i :: (j :: v))) z‖ := by
                rw [hchain, norm_mul]


/-- Pieces are nested. -/
theorem piece_append_subset {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hτ : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) (w v : List (Fin N)) :
    piece τ p r (w ++ v) ⊆ piece τ p r w := by
  cases v with
  | nil => simp [piece]
  | cons a v =>
      intro z hz
      rw [piece] at hz ⊢
      obtain ⟨ζ, hζ, hζz⟩ := hz
      refine ⟨ifsComp τ (a :: v) ζ,
        ifsComp_mapsTo_closedBall hr hτ (a :: v) (List.cons_ne_nil a v) hζ, ?_⟩
      rw [← hζz, ifsComp_append]
      rfl

/-- Bound on the derivative of a composition on the inner ball. -/
theorem norm_deriv_ifsComp_le {τ : Fin N → ℂ → ℂ} {p : ℂ} {r θ : ℝ} (hr : 0 < r)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2)))
    (hderiv : ∀ i, ∀ z ∈ closedBall p (r / 2), ‖deriv (τ i) z‖ ≤ θ) :
    ∀ w : List (Fin N), w ≠ [] → ∀ z ∈ closedBall p (r / 2),
      ‖deriv (ifsComp τ w) z‖ ≤ θ ^ w.length := by
  intro w
  induction w with
  | nil => intro h; exact absurd rfl h
  | cons i w ih =>
      intro hw z hz
      cases w with
      | nil =>
          have heq : deriv (ifsComp τ [i]) z = deriv (τ i) z := by
            simp [ifsComp]
          rw [heq]
          simpa using hderiv i z hz
      | cons j v =>
          have hzr : z ∈ ball p r := by
            rw [mem_closedBall] at hz; rw [mem_ball]; linarith [hz, hr]
          have hinner : DifferentiableAt ℂ (ifsComp τ (j :: v)) z :=
            ifsComp_differentiableAt hr hdiff hmaps (j :: v) (List.cons_ne_nil j v) z hzr
          have hmem : ifsComp τ (j :: v) z ∈ closedBall p (r / 2) :=
            ifsComp_mapsTo_closedBall hr hmaps (j :: v) (List.cons_ne_nil j v) hz
          have hmemr : ifsComp τ (j :: v) z ∈ ball p r := by
            rw [mem_closedBall] at hmem; rw [mem_ball]; linarith [hmem, hr]
          have houter : DifferentiableAt ℂ (τ i) (ifsComp τ (j :: v) z) :=
            (hdiff i).differentiableAt (isOpen_ball.mem_nhds hmemr)
          have hchain : deriv (ifsComp τ (i :: (j :: v))) z
              = deriv (τ i) (ifsComp τ (j :: v) z) * deriv (ifsComp τ (j :: v)) z :=
            deriv_comp z houter hinner
          have h1 := hderiv i (ifsComp τ (j :: v) z) hmem
          have h2 := ih (List.cons_ne_nil j v) z hz
          have hθ : 0 ≤ θ := le_trans (norm_nonneg _) h1
          calc ‖deriv (ifsComp τ (i :: (j :: v))) z‖
              = ‖deriv (τ i) (ifsComp τ (j :: v) z)‖ * ‖deriv (ifsComp τ (j :: v)) z‖ := by
                rw [hchain, norm_mul]
            _ ≤ θ * θ ^ (j :: v).length := mul_le_mul h1 h2 (norm_nonneg _) hθ
            _ = θ ^ (i :: (j :: v)).length := by
                rw [show (i :: (j :: v)).length = (j :: v).length + 1 from rfl, pow_succ]
                ring

/-- An infinite word belongs to the cylinder of each of its prefixes. -/
theorem mem_cylinder_pref (ω : ℕ → Fin N) (k : ℕ) : ω ∈ MandelDim.cylinder (pref ω k) := by
  intro j hj
  simp only [pref] at hj ⊢
  rw [List.get_eq_getElem, List.getElem_map, List.getElem_range]

/-- A prefix of `pref ω k` is itself a prefix of `ω` (of its own length). -/
theorem eq_pref_of_isPrefix (ω : ℕ → Fin N) (k : ℕ) {v : List (Fin N)}
    (hv : v <+: pref ω k) : v = pref ω v.length := by
  obtain ⟨t, ht⟩ := hv
  have hlen : v.length ≤ k := by
    have h2 := congrArg List.length ht
    simp only [List.length_append, pref_length] at h2
    omega
  conv_lhs => rw [← List.take_left (l₁ := v) (l₂ := t)]
  rw [ht, pref, ← List.map_take, List.take_range, Nat.min_eq_left hlen]
  rfl

/-- Taking `j ≤ k` letters of `pref ω k` gives `pref ω j`. -/
theorem take_pref (ω : ℕ → Fin N) {j k : ℕ} (h : j ≤ k) :
    (pref ω k).take j = pref ω j := by
  rw [pref, ← List.map_take, List.take_range, Nat.min_eq_left h]
  rfl

/-- Analyticity of every composition (including the empty word). -/
theorem ifsComp_analyticAt_all {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ (w : List (Fin N)) (z : ℂ), z ∈ ball p r → AnalyticAt ℂ (ifsComp τ w) z := by
  intro w z hz
  cases w with
  | nil => simpa [ifsComp] using analyticAt_id (z := z)
  | cons i v => exact ifsComp_analyticAt hr hdiff hmaps (i :: v) (List.cons_ne_nil i v) z hz

/-- Injectivity of every composition (including the empty word). -/
theorem ifsComp_injOn_all {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hτ : ∀ i, InjOn (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ w : List (Fin N), InjOn (ifsComp τ w) (ball p r) := by
  intro w
  cases w with
  | nil => simpa [ifsComp] using injOn_id (s := ball p r)
  | cons i v => exact ifsComp_injOn hr hτ hmaps (i :: v) (List.cons_ne_nil i v)

/-- Differentiability of every composition (including the empty word). -/
theorem ifsComp_differentiableAt_all {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ (w : List (Fin N)) (z : ℂ), z ∈ ball p r → DifferentiableAt ℂ (ifsComp τ w) z :=
  fun w z hz => (ifsComp_analyticAt_all hr hdiff hmaps w z hz).differentiableAt

/-- Membership in a cylinder, in `Fin`-indexed form. -/
theorem mem_cylinder_iff {l : List (Fin N)} {ω : ℕ → Fin N} :
    ω ∈ MandelDim.cylinder l ↔ ∀ k : Fin l.length, ω k = l.get k := by
  constructor
  · intro h k; exact h k k.isLt
  · intro h k hk; exact h ⟨k, hk⟩

/-- The `Fin`-indexed description of a cylinder. -/
theorem cylinder_eq (l : List (Fin N)) :
    MandelDim.cylinder l = {ω : ℕ → Fin N | ∀ k : Fin l.length, ω k = l.get k} :=
  Set.ext fun _ => mem_cylinder_iff

/-- A word whose cylinder contains `ω` is the prefix of `ω` of its own length. -/
theorem pref_eq_of_mem_cylinder {l : List (Fin N)} {ω : ℕ → Fin N}
    (h : ω ∈ MandelDim.cylinder l) : pref ω l.length = l := by
  apply List.ext_getElem
  · simp [pref]
  · intro j h1 h2
    have h3 : ω j = l[j] := by
      have := mem_cylinder_iff.mp h ⟨j, h2⟩
      rwa [List.get_eq_getElem] at this
    simp only [pref, List.getElem_map, List.getElem_range]
    exact h3

end Work.Dim
