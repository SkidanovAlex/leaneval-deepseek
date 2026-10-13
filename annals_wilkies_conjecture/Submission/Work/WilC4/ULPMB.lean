/-
  WilC4/ULPMB : the structural breakpoint family of the ULPM proof.

  Two inputs on disk do all the o-minimal work:

  * `ulpm_crit hOM Y hY hfun` gives a `∅`-definable `Bc` with `≤ N₁` points per fibre off which
    the fibre of `Y` is continuous, its *domain* is all-or-nothing on every interval and its *zero
    set* is all-or-nothing on every interval;
  * `ulpm_mono_param hOM (RatGraph Y) …` gives a `∅`-definable `Bm` with `≤ N₃` points per fibre off
    which the doubling ratio is monotone.

  This file bundles their conjunction into `ULPMB` and adds the two families.  `ULPMB` is the
  *restricted* form valid for partial fibres (a fibre defined on a proper interval must be allowed
  to vanish identically, so `GoodFibre`'s "total off `B`" cannot hold); applying `ULPMB` to
  `UlpmTot Y` (whose fibre is total and nowhere zero by construction) does give `ULPMStruct`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ulpm_crit
import Submission.Work.WilC4.ulpm_mono_param

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr)

variable {k : ℕ}

/-- The structural conclusions of `ulpm_crit` and `ulpm_mono_param` for the ratio, bundled: off
`B` the fibre is continuous, its domain and zero set are all-or-nothing on every interval, and the
doubling ratio `RatW` is monotone.  This is the form valid for *partial* fibres; `ULPMStruct`
(which asks for totality off `B`) is what one gets by applying it to `UlpmTot Y`. -/
def ULPMB (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ)) : Prop :=
  (∀ (c : Fin k → ℝ) (a b : ℝ), a < b → (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) →
    ((∃ x ∈ Set.Ioo a b, ∃ y : ℝ, Gr Y c x y) → (∀ x ∈ Set.Ioo a b, ∃ y : ℝ, Gr Y c x y)) ∧
    ((∃ x ∈ Set.Ioo a b, Gr Y c x (0 : ℝ)) → (∀ x ∈ Set.Ioo a b, Gr Y c x (0 : ℝ))) ∧
    (∀ x ∈ Set.Ioo a b, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b, ∀ y y' : ℝ,
      |x' - x| < δ → Gr Y c x y → Gr Y c x' y' → |y' - y| < ε)) ∧
  (∀ (c : Fin k → ℝ) (a b : ℝ), a < b → (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) →
    ∀ x₁ x₂ x₃ w₁ w₂ w₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
      x₁ < x₂ → x₂ < x₃ → RatW Y c x₁ w₁ → RatW Y c x₂ w₂ → RatW Y c x₃ w₃ →
      (w₁ ≤ w₂ ∧ w₂ ≤ w₃) ∨ (w₃ ≤ w₂ ∧ w₂ ≤ w₁))

/-- **The structural family.**  For a `∅`-definable family of graphs `Y` there are a uniform bound
`N` and a `∅`-definable breakpoint family `B` with `|B_c| ≤ N` and `ULPMB Y B`: off `B` the fibre
is continuous with all-or-nothing domain and zero set, and the doubling ratio is monotone.

The ratio-monotonicity input is taken as a hypothesis (it is `ulpm_mono_param` applied to
`Route.RatGraph Y`, available once `ratGraph_definable` is imported). -/
theorem exists_ulpmB (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (Bm : Set (Fin (k + 1) → ℝ)) (hBm : (∅ : Set ℝ).Definable LRc Bm) (Nm : ℕ)
    (hBmcard : ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ Bm}.encard ≤ Nm)
    (hmono : ∀ (c : Fin k → ℝ) (a b : ℝ), a < b → (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ Bm) →
      ∀ x₁ x₂ x₃ w₁ w₂ w₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
        x₁ < x₂ → x₂ < x₃ → RatW Y c x₁ w₁ → RatW Y c x₂ w₂ → RatW Y c x₃ w₃ →
        (w₁ ≤ w₂ ∧ w₂ ≤ w₃) ∨ (w₃ ≤ w₂ ∧ w₂ ≤ w₁)) :
    ∃ N : ℕ, ∃ B : Set (Fin (k + 1) → ℝ), (∅ : Set ℝ).Definable LRc B ∧
      (∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B}.encard ≤ N) ∧ ULPMB Y B := by
  obtain ⟨N₁, Bc, hBc, hN₁, hcrit⟩ := ulpm_crit hOM Y hY hfun
  refine ⟨N₁ + Nm, Bc ∪ Bm, hBc.union hBm, ?_, ?_⟩
  · intro c
    have hfib : {x : ℝ | Fin.cons x c ∈ Bc ∪ Bm} =
        {x : ℝ | Fin.cons x c ∈ Bc} ∪ {x : ℝ | Fin.cons x c ∈ Bm} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [hfib]
    calc (({x : ℝ | Fin.cons x c ∈ Bc} ∪ {x : ℝ | Fin.cons x c ∈ Bm}).encard)
        ≤ ({x : ℝ | Fin.cons x c ∈ Bc}).encard + ({x : ℝ | Fin.cons x c ∈ Bm}).encard :=
          Set.encard_union_le _ _
      _ ≤ ((N₁ : ENat) + (Nm : ENat)) := add_le_add (hN₁ c) (hBmcard c)
      _ = ((N₁ + Nm : ℕ) : ENat) := by rw [Nat.cast_add]
  · exact ⟨fun c a b hab havb => hcrit c a b hab (fun x hx hxc => havb x hx (Or.inl hxc)),
           fun c a b hab havb => hmono c a b hab (fun x hx hxm => havb x hx (Or.inr hxm))⟩

/-- The fibre of `UlpmTot Y` is total. -/
theorem ulpmTot_total (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x : ℝ) :
    ∃ y : ℝ, Gr (UlpmTot Y) c x y := by
  by_cases h : ∃ y : ℝ, Gr Y c x y ∧ y ≠ 0
  · obtain ⟨y, hy, hyne⟩ := h
    exact ⟨y, (ulpmTot_gr_iff Y c x y).mpr (Or.inl ⟨hy, hyne⟩)⟩
  · exact ⟨1, (ulpmTot_gr_iff Y c x 1).mpr (Or.inr ⟨rfl, fun y' hy' => h ⟨y', hy'.1, hy'.2⟩⟩)⟩

/-- The fibre of `UlpmTot Y` is nowhere zero. -/
theorem ulpmTot_ne (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x y : ℝ)
    (h : Gr (UlpmTot Y) c x y) : y ≠ 0 := by
  rcases (ulpmTot_gr_iff Y c x y).mp h with ⟨-, hy⟩ | ⟨hy, -⟩
  · exact hy
  · rw [hy]; norm_num

/-- `UlpmTot Y` is a family of graphs as soon as `Y` is. -/
theorem ulpmTot_functional {Y : Set (Fin (k + 2) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y') :
    ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr (UlpmTot Y) c x y → Gr (UlpmTot Y) c x y' → y = y' := by
  intro c x y y' hy hy'
  rcases (ulpmTot_gr_iff Y c x y).mp hy with ⟨hg, hyne⟩ | ⟨hy1, hall⟩
  · rcases (ulpmTot_gr_iff Y c x y').mp hy' with ⟨hg', hy'ne⟩ | ⟨hy'1, hall'⟩
    · exact hfun c x y y' hg hg'
    · exact absurd (hall' y ⟨hg, hyne⟩) (fun h => h)
  · rcases (ulpmTot_gr_iff Y c x y').mp hy' with ⟨hg', hy'ne⟩ | ⟨hy'1, hall'⟩
    · exact absurd (hall y' ⟨hg', hy'ne⟩) (fun h => h)
    · rw [hy1, hy'1]

/-- `ULPMB` for the totalised family gives `ULPMStruct`: totality and nonvanishing supply the two
extra clauses of `GoodFibre`. -/
theorem ulpmStruct_of_ulpmB_tot {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (h : ULPMB (UlpmTot Y) B) : ULPMStruct (UlpmTot Y) B := by
  obtain ⟨hcrit, hmono⟩ := h
  refine ⟨?_, hmono⟩
  intro c a b hab havb
  obtain ⟨hdich, -, hcont⟩ := hcrit c a b hab havb
  have hfunT := ulpmTot_functional hfun
  refine ⟨fun x _ => ?_, fun x _ y hy => ulpmTot_ne Y c x y hy, fun x hx ε hε => ?_⟩
  · obtain ⟨y, hy⟩ := ulpmTot_total Y c x
    exact ⟨y, hy, fun y' hy' => hfunT c x y' y hy' hy⟩
  · exact hcont x hx ε hε

end Work.WilC4
