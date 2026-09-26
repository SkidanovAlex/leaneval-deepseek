/- Record of the received request (quoted verbatim, truncated just before the proof placeholder).
theorem intervalHomeo_extend {a b c d : ℝ} (h0a : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hcd : c < d)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d})) :
    ∃ (c' d' : ℝ), c' ≤ c ∧ d ≤ d' ∧ c' < d' ∧
      ∃ e' : ({x : ℝ // x ∈ Set.Ioo 0 1}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c' d'}),
        ∀ (x : ℝ) (hx : x ∈ Set.Ioo a b),
          ((e' ⟨x, ⟨lt_of_le_of_lt h0a hx.1, lt_of_lt_of_le hx.2 hb1⟩⟩ :
            {x : ℝ // x ∈ Set.Ioo c' d'}) : ℝ) =
            ((e ⟨x, hx⟩ : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ)

end Commons.Topology.Homeomorph := by
-/

import Mathlib
import Submission.Commons.Topology.Homeomorph.intervalHomeo_coord_strictMono_or_anti

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Commons.Topology.Homeomorph

noncomputable section

def extTotal {a b c d : ℝ} (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    (x : ℝ) : ℝ :=
  if h1 : x < a then x + (c - a)
  else if h2 : b < x then x + (d - b)
  else if h3 : x = a then c
  else if h4 : x = b then d
  else
    (e ⟨x, ⟨lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h3), lt_of_le_of_ne (not_lt.mp h2) h4⟩⟩ : ℝ)

theorem extTotal_of_lt {a b c d : ℝ} (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h : x < a) : extTotal e x = x + (c - a) := by
  simp [extTotal, h]

theorem extTotal_of_gt {a b c d : ℝ} (hab : a < b)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h : b < x) : extTotal e x = x + (d - b) := by
  have hna : ¬ x < a := by linarith
  simp [extTotal, hna, h]

theorem extTotal_of_eq_a {a b c d : ℝ} (hab : a < b)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h : x = a) : extTotal e x = c := by
  subst x
  have hnb : ¬ b < a := by linarith
  simp [extTotal, hnb]

theorem extTotal_of_eq_b {a b c d : ℝ} (hab : a < b)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h : x = b) : extTotal e x = d := by
  subst x
  have hna : ¬ b < a := by linarith
  have hne_a : b ≠ a := by linarith
  simp [extTotal, hna, hne_a]

theorem extTotal_of_mem {a b c d : ℝ} (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h1 : a < x) (h2 : x < b) :
    extTotal e x = (e ⟨x, ⟨h1, h2⟩⟩ : ℝ) := by
  simp [extTotal, not_lt.mpr (le_of_lt h1), not_lt.mpr (le_of_lt h2), ne_of_gt h1, ne_of_lt h2]

theorem extTotal_mem {a b c d : ℝ} (h0a : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : extTotal e x ∈ Set.Ioo (c - a) (d + 1 - b) := by
  by_cases h1 : x < a
  · rw [extTotal_of_lt e h1]
    constructor <;> linarith [hx.1, hx.2, h1]
  · by_cases h2 : b < x
    · rw [extTotal_of_gt hab e h2]
      constructor <;> linarith [hx.1, hx.2, h2]
    · by_cases h3 : x = a
      · rw [extTotal_of_eq_a hab e h3]
        constructor <;> linarith [hx.1, hx.2, h3, h0a, hb1, hcd]
      · by_cases h4 : x = b
        · rw [extTotal_of_eq_b hab e h4]
          constructor <;> linarith [hx.1, hx.2, h4, h0a, hb1, hcd]
        · rw [extTotal_of_mem e (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h3))
            (lt_of_le_of_ne (not_lt.mp h2) h4)]
          have hv : (e ⟨x, ⟨lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h3),
            lt_of_le_of_ne (not_lt.mp h2) h4⟩⟩ : ℝ) ∈ Set.Ioo c d :=
            (e ⟨x, ⟨lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h3),
              lt_of_le_of_ne (not_lt.mp h2) h4⟩⟩).2
          constructor <;> linarith [h0a, hb1, hv.1, hv.2]

-- Boundary comparison lemmas ----------------------------------------------

/-- Values on the left piece lie below `c`. -/
theorem extTotal_lt_c {a b c d : ℝ}
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h : x < a) : extTotal e x < c := by
  rw [extTotal_of_lt e h]
  linarith

/-- `c` is a strict lower bound for values at points strictly right of `a`. -/
theorem c_lt_extTotal {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h : a < x) : c < extTotal e x := by
  by_cases hxb : x < b
  · rw [extTotal_of_mem e h hxb]
    exact (e ⟨x, ⟨h, hxb⟩⟩ : {x : ℝ // x ∈ Set.Ioo c d}).2.1
  · have hxge : b ≤ x := not_lt.mp hxb
    rcases lt_or_eq_of_le hxge with hxgt | hxeq
    · rw [extTotal_of_gt hab e hxgt]
      linarith [hcd]
    · rw [extTotal_of_eq_b hab e hxeq.symm]
      exact hcd

/-- `c` is a lower bound for values at points right of `a` (including `a`). -/
theorem extTotal_ge_c {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h : a ≤ x) : c ≤ extTotal e x := by
  rcases lt_or_eq_of_le h with hxgt | hxeq
  · exact le_of_lt (c_lt_extTotal hab hcd e hxgt)
  · rw [extTotal_of_eq_a hab e hxeq.symm]

/-- Values on the left-and-middle region (points left of `b`) lie below `d`. -/
theorem extTotal_lt_d {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h : x < b) : extTotal e x < d := by
  by_cases hxa : x < a
  · rw [extTotal_of_lt e hxa]
    linarith [hcd]
  · have hxge : a ≤ x := not_lt.mp hxa
    rcases lt_or_eq_of_le hxge with hxgt | hxeq
    · rw [extTotal_of_mem e hxgt h]
      exact (e ⟨x, ⟨hxgt, h⟩⟩ : {x : ℝ // x ∈ Set.Ioo c d}).2.2
    · rw [extTotal_of_eq_a hab e hxeq.symm]
      exact hcd

/-- Values on the right piece lie above `d`. -/
theorem d_lt_extTotal {a b c d : ℝ} (hab : a < b)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h : b < x) : d < extTotal e x := by
  rw [extTotal_of_gt hab e h]
  linarith

/-- `d` is a lower bound for values at points right of `b` (including `b`). -/
theorem extTotal_ge_d {a b c d : ℝ} (hab : a < b)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    {x : ℝ} (h : b ≤ x) : d ≤ extTotal e x := by
  rcases lt_or_eq_of_le h with hxgt | hxeq
  · exact le_of_lt (d_lt_extTotal hab e hxgt)
  · rw [extTotal_of_eq_b hab e hxeq.symm]

-- Monotonicity of the extension (increasing case) -------------------------

/-- The extension is strictly increasing. -/
theorem extTotal_strictMono {a b c d : ℝ} (h0a : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    (hmono : StrictMono (fun t : {x : ℝ // x ∈ Set.Ioo a b} => (e t : ℝ))) :
    StrictMono (fun x : {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1} => extTotal e (x : ℝ)) := by
  intro x y hxy
  have hxyv : (x : ℝ) < (y : ℝ) := hxy
  change extTotal e (x : ℝ) < extTotal e (y : ℝ)
  by_cases hyb : (y : ℝ) < b
  · -- both below b: x < y < b
    by_cases hxa : (x : ℝ) < a
    · -- x < a
      by_cases hya : (y : ℝ) < a
      · -- both on left translation piece
        have hxv : extTotal e (x : ℝ) = (x : ℝ) + (c - a) := extTotal_of_lt e hxa
        have hyv : extTotal e (y : ℝ) = (y : ℝ) + (c - a) := extTotal_of_lt e hya
        rw [hxv, hyv]
        linarith
      · -- x < a ≤ y: F x < c ≤ F y
        exact lt_of_lt_of_le (extTotal_lt_c e hxa)
          (extTotal_ge_c hab hcd e (not_lt.mp hya))
    · -- a ≤ x
      by_cases hxeqa : (x : ℝ) = a
      · -- x = a < y < b: F x = c < F y
        have hya : a < (y : ℝ) := by linarith
        rw [extTotal_of_eq_a hab e hxeqa]
        exact c_lt_extTotal hab hcd e hya
      · -- a < x < y < b: use monotonicity of e
        have hxga : a < (x : ℝ) := lt_of_le_of_ne (not_lt.mp hxa) (Ne.symm hxeqa)
        have hxyb : (x : ℝ) < b := lt_trans hxyv hyb
        have hyga : a < (y : ℝ) := lt_trans hxga hxyv
        have hxv : extTotal e (x : ℝ) = (e ⟨(x : ℝ), ⟨hxga, hxyb⟩⟩ : ℝ) :=
          extTotal_of_mem e hxga hxyb
        have hyv : extTotal e (y : ℝ) = (e ⟨(y : ℝ), ⟨hyga, hyb⟩⟩ : ℝ) :=
          extTotal_of_mem e hyga hyb
        rw [hxv, hyv]
        have hu_lt : (⟨(x : ℝ), ⟨hxga, hxyb⟩⟩ : {x : ℝ // x ∈ Set.Ioo a b}) <
            ⟨(y : ℝ), ⟨hyga, hyb⟩⟩ := hxyv
        exact hmono hu_lt
  · -- ¬ (y < b): b ≤ y
    have hyge : b ≤ (y : ℝ) := not_lt.mp hyb
    by_cases hxb : (x : ℝ) < b
    · -- x < b ≤ y: F x < d ≤ F y
      exact lt_of_lt_of_le (extTotal_lt_d hab hcd e hxb) (extTotal_ge_d hab e hyge)
    · -- b ≤ x < y
      have hxge : b ≤ (x : ℝ) := not_lt.mp hxb
      by_cases hxeqb : (x : ℝ) = b
      · -- x = b < y: F x = d < F y
        have hygb : b < (y : ℝ) := by linarith
        rw [extTotal_of_eq_b hab e hxeqb]
        exact d_lt_extTotal hab e hygb
      · -- b < x < y: right translation piece
        have hxgb : b < (x : ℝ) := lt_of_le_of_ne hxge (Ne.symm hxeqb)
        have hygb : b < (y : ℝ) := lt_trans hxgb hxyv
        have hxv : extTotal e (x : ℝ) = (x : ℝ) + (d - b) := extTotal_of_gt hab e hxgb
        have hyv : extTotal e (y : ℝ) = (y : ℝ) + (d - b) := extTotal_of_gt hab e hygb
        rw [hxv, hyv]
        linarith

-- Surjectivity ------------------------------------------------------------

/-- The extension is surjective onto the target interval. -/
theorem extTotal_surjOn {a b c d : ℝ} (h0a : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    (y : {y : ℝ // y ∈ Set.Ioo (c - a) (d + 1 - b)}) :
    ∃ x : {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}, extTotal e (x : ℝ) = (y : ℝ) := by
  have hy1 : c - a < (y : ℝ) := y.2.1
  have hy2 : (y : ℝ) < d + 1 - b := y.2.2
  rcases lt_trichotomy (y : ℝ) c with hyc | hyeqc | hygc
  · -- y < c : preimage x = y + a - c on the left piece
    let x : ℝ := (y : ℝ) + a - c
    have hx0 : 0 < x := by dsimp [x]; linarith
    have hxa : x < a := by dsimp [x]; linarith
    have hx1 : x < 1 := lt_of_lt_of_le hxa (le_trans (le_of_lt hab) hb1)
    refine ⟨⟨x, ⟨hx0, hx1⟩⟩, ?_⟩
    have hxv : extTotal e x = x + (c - a) := extTotal_of_lt e hxa
    rw [hxv]
    dsimp [x]
    ring
  · -- y = c : preimage x = a (needs 0 < a)
    have ha0 : 0 < a := by linarith
    have ha1 : a < 1 := lt_of_lt_of_le hab hb1
    refine ⟨⟨a, ⟨ha0, ha1⟩⟩, ?_⟩
    have hxv : extTotal e a = c := extTotal_of_eq_a hab e rfl
    rw [hxv]
    exact hyeqc.symm
  · -- c < y
    rcases lt_trichotomy (y : ℝ) d with hyd | hyeqd | hygd
    · -- c < y < d : preimage via e.symm
      let t : {t : ℝ // t ∈ Set.Ioo c d} := ⟨(y : ℝ), ⟨hygc, hyd⟩⟩
      let x0 : {x : ℝ // x ∈ Set.Ioo a b} := e.symm t
      have hx0_1 : 0 < (x0 : ℝ) := lt_of_le_of_lt h0a x0.2.1
      have hx0_2 : (x0 : ℝ) < 1 := lt_of_lt_of_le x0.2.2 hb1
      refine ⟨⟨(x0 : ℝ), ⟨hx0_1, hx0_2⟩⟩, ?_⟩
      have hxv : extTotal e (x0 : ℝ) = (e ⟨(x0 : ℝ), ⟨x0.2.1, x0.2.2⟩⟩ : ℝ) :=
        extTotal_of_mem e x0.2.1 x0.2.2
      have het : (e ⟨(x0 : ℝ), ⟨x0.2.1, x0.2.2⟩⟩ : ℝ) = (y : ℝ) := by
        have hsub : (⟨(x0 : ℝ), ⟨x0.2.1, x0.2.2⟩⟩ : {x : ℝ // x ∈ Set.Ioo a b}) = x0 := by
          apply Subtype.ext
          rfl
        calc
          (e ⟨(x0 : ℝ), ⟨x0.2.1, x0.2.2⟩⟩ : ℝ) = (e x0 : ℝ) := by rw [hsub]
          _ = (t : ℝ) := by
            exact congrArg (fun z : {x : ℝ // x ∈ Set.Ioo c d} => (z : ℝ))
              (e.apply_symm_apply t)
          _ = (y : ℝ) := by rfl
      rw [hxv, het]
    · -- y = d : preimage x = b (needs b < 1)
      have hb1s : b < 1 := by linarith
      have hb0 : 0 < b := lt_of_le_of_lt h0a hab
      refine ⟨⟨b, ⟨hb0, hb1s⟩⟩, ?_⟩
      have hxv : extTotal e b = d := extTotal_of_eq_b hab e rfl
      rw [hxv]
      exact hyeqd.symm
    · -- d < y : preimage x = y + b - d on the right piece
      let x : ℝ := (y : ℝ) + b - d
      have hb0 : 0 < b := lt_of_le_of_lt h0a hab
      have hxb : b < x := by dsimp [x]; linarith
      have hx0 : 0 < x := lt_trans hb0 hxb
      have hx1 : x < 1 := by dsimp [x]; linarith
      refine ⟨⟨x, ⟨hx0, hx1⟩⟩, ?_⟩
      have hxv : extTotal e x = x + (d - b) := extTotal_of_gt hab e hxb
      rw [hxv]
      dsimp [x]
      ring

/-- The monotone extension is a homeomorphism onto `(c-a, d+1-b)`, agreeing
with `e` on `(a,b)`. -/
theorem intervalHomeo_extend_inc {a b c d : ℝ} (h0a : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hcd : c < d) (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    (hmono : StrictMono (fun t : {x : ℝ // x ∈ Set.Ioo a b} => (e t : ℝ))) :
    ∃ e' : ({x : ℝ // x ∈ Set.Ioo 0 1}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo (c - a) (d + 1 - b)}),
      ∀ (x : ℝ) (hx : x ∈ Set.Ioo a b),
        ((e' ⟨x, ⟨lt_of_le_of_lt h0a hx.1, lt_of_lt_of_le hx.2 hb1⟩⟩ :
            {y : ℝ // y ∈ Set.Ioo (c - a) (d + 1 - b)}) : ℝ) =
          ((e ⟨x, hx⟩ : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ) := by
  classical
  let F : {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1} → {y : ℝ // y ∈ Set.Ioo (c - a) (d + 1 - b)} :=
    fun x => ⟨extTotal e (x : ℝ), extTotal_mem h0a hab hb1 hcd e x.2⟩
  have hFmono : StrictMono F := by
    intro x y hxy
    change extTotal e (x : ℝ) < extTotal e (y : ℝ)
    exact extTotal_strictMono h0a hab hb1 hcd e hmono hxy
  have hFsurj : Function.Surjective F := by
    intro y
    rcases extTotal_surjOn h0a hab hb1 hcd e y with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  let G : {y : ℝ // y ∈ Set.Ioo (c - a) (d + 1 - b)} → {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1} :=
    fun y => Classical.choose (hFsurj y)
  have hG_right : ∀ y, F (G y) = y := by
    intro y
    exact Classical.choose_spec (hFsurj y)
  have hG_left : ∀ x, G (F x) = x := by
    intro x
    apply hFmono.injective
    simpa [G] using hG_right (F x)
  let e0 : {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1} ≃ {y : ℝ // y ∈ Set.Ioo (c - a) (d + 1 - b)} :=
    { toFun := F
      invFun := G
      left_inv := hG_left
      right_inv := hG_right }
  let iso : ({x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}) ≃o
      ({y : ℝ // y ∈ Set.Ioo (c - a) (d + 1 - b)}) :=
    { toEquiv := e0
      map_rel_iff' := by
        intro x y
        constructor
        · intro hle
          by_contra hnot
          have hytx : y < x := lt_of_not_ge hnot
          exact (not_lt_of_ge hle) (hFmono hytx)
        · intro hxy
          rcases lt_or_eq_of_le hxy with hlt | heq
          · exact le_of_lt (hFmono hlt)
          · rw [heq] }
  refine ⟨iso.toHomeomorph, ?_⟩
  intro x hx
  change extTotal e x = (e ⟨x, hx⟩ : ℝ)
  exact extTotal_of_mem e hx.1 hx.2

-- ==================== Decreasing case via reflection ======================

/-- The reflection `x ↦ 1 - x` maps `(1-b, 1-a)` onto `(a,b)`. -/
noncomputable def reflDown (a b : ℝ) :
    ({x : ℝ // x ∈ Set.Ioo (1 - b) (1 - a)}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo a b}) := by
  let S : Type := {x : ℝ // x ∈ Set.Ioo (1 - b) (1 - a)}
  let T : Type := {x : ℝ // x ∈ Set.Ioo a b}
  let F : S → T := fun x => ⟨1 - (x : ℝ), by
    constructor <;> linarith [x.2.1, x.2.2]⟩
  let G : T → S := fun y => ⟨1 - (y : ℝ), by
    constructor <;> linarith [y.2.1, y.2.2]⟩
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    ring
  have hGF : Function.RightInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    ring
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_const.sub continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_const.sub continuous_subtype_val
  let e0 : S ≃ T :=
    { toFun := F
      invFun := G
      left_inv := hFG
      right_inv := hGF }
  exact Homeomorph.mk e0 hFc hGc

/-- Value lemma for `reflDown`. -/
theorem reflDown_val (a b : ℝ) (x : {x : ℝ // x ∈ Set.Ioo (1 - b) (1 - a)}) :
    ((reflDown a b x : {x : ℝ // x ∈ Set.Ioo a b}) : ℝ) = 1 - (x : ℝ) := by
  rfl

/-- The reflection `x ↦ 1 - x` of the open unit interval onto itself. -/
noncomputable def reflUnit : ({x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ
    ({x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}) := by
  let S : Type := {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}
  let F : S → S := fun x => ⟨1 - (x : ℝ), by
    constructor <;> linarith [x.2.1, x.2.2]⟩
  let G : S → S := fun x => ⟨1 - (x : ℝ), by
    constructor <;> linarith [x.2.1, x.2.2]⟩
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    ring
  have hGF : Function.RightInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    ring
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_const.sub continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_const.sub continuous_subtype_val
  let e0 : S ≃ S :=
    { toFun := F
      invFun := G
      left_inv := hFG
      right_inv := hGF }
  exact Homeomorph.mk e0 hFc hGc

/-- Value lemma for `reflUnit`. -/
theorem reflUnit_val (x : {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}) :
    ((reflUnit x : {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}) : ℝ) = 1 - (x : ℝ) := by
  rfl

/-- The antitone extension is a homeomorphism onto
`(c - (1-b), d + 1 - (1-a))`, agreeing with `e` on `(a,b)`. -/
theorem intervalHomeo_extend_dec {a b c d : ℝ} (h0a : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hcd : c < d) (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}))
    (hanti : StrictAnti (fun t : {x : ℝ // x ∈ Set.Ioo a b} => (e t : ℝ))) :
    ∃ e' : ({x : ℝ // x ∈ Set.Ioo 0 1}) ≃ₜ
        ({x : ℝ // x ∈ Set.Ioo (c - (1 - b)) (d + 1 - (1 - a))}),
      ∀ (x : ℝ) (hx : x ∈ Set.Ioo a b),
        ((e' ⟨x, ⟨lt_of_le_of_lt h0a hx.1, lt_of_lt_of_le hx.2 hb1⟩⟩ :
            {y : ℝ // y ∈ Set.Ioo (c - (1 - b)) (d + 1 - (1 - a))}) : ℝ) =
          ((e ⟨x, hx⟩ : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ) := by
  let ρ : ({x : ℝ // x ∈ Set.Ioo (1 - b) (1 - a)}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo a b}) :=
    reflDown a b
  let g : ({x : ℝ // x ∈ Set.Ioo (1 - b) (1 - a)}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d}) :=
    ρ.trans e
  have hgmono : StrictMono
      (fun t : {x : ℝ // x ∈ Set.Ioo (1 - b) (1 - a)} => (g t : ℝ)) := by
    intro t1 t2 h12
    have h12v : (t1 : ℝ) < (t2 : ℝ) := h12
    have hρlt : ((ρ t2 : {x : ℝ // x ∈ Set.Ioo a b}) : ℝ) <
        ((ρ t1 : {x : ℝ // x ∈ Set.Ioo a b}) : ℝ) := by
      rw [reflDown_val, reflDown_val]
      linarith
    have he12 : ((e (ρ t1) : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ) <
        ((e (ρ t2) : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ) := by
      exact hanti hρlt
    change ((g t1 : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ) <
      ((g t2 : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ)
    simpa [g] using he12
  rcases intervalHomeo_extend_inc (h0a := by linarith) (hab := by linarith)
      (hb1 := by linarith) (hcd := hcd) (e := g) hgmono with ⟨g', hgext⟩
  let R : ({x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}) :=
    reflUnit
  refine ⟨R.trans g', ?_⟩
  intro x hx
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt h0a hx.1, lt_of_lt_of_le hx.2 hb1⟩
  have hR : ((R ⟨x, hx01⟩ : {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}) : ℝ) = 1 - x := by
    exact reflUnit_val ⟨x, hx01⟩
  have hw : 1 - x ∈ Set.Ioo (1 - b) (1 - a) := by
    constructor <;> linarith [hx.1, hx.2]
  have hw01 : 1 - x ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2, h0a, hb1]
  have hgextw := hgext (1 - x) hw
  change ((g' (R ⟨x, hx01⟩) : {y : ℝ // y ∈ Set.Ioo (c - (1 - b)) (d + 1 - (1 - a))}) : ℝ) =
    ((e ⟨x, hx⟩ : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ)
  have hRu : (R ⟨x, hx01⟩ : {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}) = ⟨1 - x, hw01⟩ := by
    apply Subtype.ext
    exact hR
  rw [hRu]
  have hgextw' : ((g' ⟨1 - x, hw01⟩ : {y : ℝ // y ∈ Set.Ioo (c - (1 - b)) (d + 1 - (1 - a))}) : ℝ) =
      ((g ⟨1 - x, hw⟩ : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ) := hgextw
  rw [hgextw']
  change ((e (ρ ⟨1 - x, hw⟩) : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ) =
    ((e ⟨x, hx⟩ : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ)
  have hρv : ((ρ ⟨1 - x, hw⟩ : {x : ℝ // x ∈ Set.Ioo a b}) : ℝ) = x := by
    rw [reflDown_val]
    ring
  have hρeq : (ρ ⟨1 - x, hw⟩ : {x : ℝ // x ∈ Set.Ioo a b}) = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact hρv
  rw [hρeq]


-- ==================== Main theorem ======================

/-- Any homeomorphism `e : (a,b) ≃ₜ (c,d)` between open real intervals with
`(a,b) ⊆ (0,1)` (i.e. `0 ≤ a < b ≤ 1`) extends to a homeomorphism
`e' : (0,1) ≃ₜ (c',d')` of the whole unit interval onto a (possibly larger)
open interval, agreeing with `e` on `(a,b)` (as real values) and with
`(c,d) ⊆ (c',d')`.  Proof idea: `e` is strictly monotone or antitone
(`intervalHomeo_coord_strictMono_or_anti`); its coordinate map reaches the
end values `c,d` at the ends of `(a,b)` (surjectivity + monotonicity), so
glue two affine pieces onto the left of `a` and right of `b` with matching
end values. -/
theorem intervalHomeo_extend {a b c d : ℝ} (h0a : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hcd : c < d)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d})) :
    ∃ (c' d' : ℝ), c' ≤ c ∧ d ≤ d' ∧ c' < d' ∧
      ∃ e' : ({x : ℝ // x ∈ Set.Ioo 0 1}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c' d'}),
        ∀ (x : ℝ) (hx : x ∈ Set.Ioo a b),
          ((e' ⟨x, ⟨lt_of_le_of_lt h0a hx.1, lt_of_lt_of_le hx.2 hb1⟩⟩ :
            {x : ℝ // x ∈ Set.Ioo c' d'}) : ℝ) =
            ((e ⟨x, hx⟩ : {x : ℝ // x ∈ Set.Ioo c d}) : ℝ) := by
  rcases intervalHomeo_coord_strictMono_or_anti hab hcd e with hinc | hdec
  · rcases intervalHomeo_extend_inc h0a hab hb1 hcd e hinc with ⟨e', hext⟩
    refine ⟨c - a, d + 1 - b, ?_, ?_, ?_, e', hext⟩
    · linarith
    · linarith
    · linarith [h0a, hb1, hcd]
  · rcases intervalHomeo_extend_dec h0a hab hb1 hcd e hdec with ⟨e', hext⟩
    refine ⟨c - (1 - b), d + 1 - (1 - a), ?_, ?_, ?_, e', hext⟩
    · linarith
    · linarith
    · linarith [h0a, hb1, hcd]


end

end Commons.Topology.Homeomorph
