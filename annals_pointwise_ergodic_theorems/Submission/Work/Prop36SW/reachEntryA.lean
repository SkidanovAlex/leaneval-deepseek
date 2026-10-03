import Mathlib
import Submission.Work.Prop36SW.chainRun
import Submission.Work.Prop36SW.entryWindowData
import Submission.Work.Prop36SW.slotCoeffFlatBoundMul

/-!
# `Work.Prop36SW.reachEntryA`: the entry state of the §5 chain

`Work.Prop36SW.Reach D d c m` (see `chainRun.lean`) is the state-reachability predicate of the
round-by-round chain of `Work.Peluse.prop36SW_of_ladderA`.  Its level `Λ` and multiplicity function
`kω` are quantified **before** `A₀` (the target `Work.Peluse.C46.Prop36SW` fixes the level before
choosing `A₀`), while the remaining constants `c₀, e₀, M₀, Cs` are quantified *after* `A₀` — they are
allowed to depend on it, since they absorb the `A₀`-dependent ambient inflations.

This module proves the **entry** of the chain at the top slot level `m = d - 2` (so that
`d - 1 - m = 1`, i.e. `Λ = 1! = 1`), with the `A₀`-free data `Λ = 1`, `kω ≡ 1` and with the
`A₀`-dependent constants produced by `entryWindowData`.

## The route

The coefficient bound of `Work.Prop36SW.chainEntry`'s `chainEntry` is *false* in general (the
level-`(d-2)` direction reads all levels `0 ≤ j ≤ d-2`, so the bound must involve the total slot count
`sSup D d`); we therefore reproduce the entry directly from the proved ingredients:

1. `Work.Prop36SW.slotCoeffFlatBoundMul`: on `D.parBox (d-1) H`,
   `|slotCoeff D d c (d-2) ·| · (H+1)² ≤ 2|c| d! (sSup D d + 1)^{d-2} (H+1)^d`;
2. `Work.Prop36SW.entryWindowData`: window bookkeeping — with `b := 2|c| d! (sSup D d+1)^{d-2}`
   there are `N ≤ N₀ ≤ N₂` with `(H+1)² ≤ N₀`, `b (H+1)^d ≤ N₀`, `ambK D d c (H+1)^d ≤ N₂`,
   `N₂ ≤ Cw·N` for a *data-independent* `Cw` (so the strength ratio `|symIcc N|/|symIcc N₂|` is
   bounded below by `1/(2Cw+1)`);
3. `Work.Prop36SW.initialStateBox D (d-2) c N₀ H f (r η)` at the inflated window `N₀`
   (`r := |symIcc N|/|symIcc N₀|`), with the family average transported by
   `Work.Prop36SW.famAvg_window_ratio_le`;
4. `Work.Peluse.Prop36SW.pFlat_one` + `Work.Prop36SW.LStateBoxAbsIff` to replace the absolute
   value of `slotCoeff` by the signed `pFlat D d c (d-2) 1`;
5. `Work.Prop36SW.LStateBoxMonoAmbient` to inflate `N₀ → N₂`, and `entryWindowData`'s strength
   ratio to read off `c₀ η^{e₀} ≤ γ` with the data-independent `c₀ := (2^{1+2|I_{d-1}|}(2Cw+1))⁻¹`,
   `e₀ := 1`.

The régime constants are `Cs := 1`, `M₀ := 1` (the entry needs no density hypothesis — that is the
point of `initialStateBox`); the subsequent rounds enlarge them as the chain descends. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

open Work.Peluse
open Work.Peluse.UControl
open Work.Peluse.Prop36SW

/-- **The entry of the §5 chain at slot level `d - 2`, uniformly in `A₀`.** -/
theorem reachEntryA (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ)
    (hd : 2 ≤ d) (hc : c ≠ 0) :
    Work.Prop36SW.Reach D d c (d - 2) := by
  classical
  refine ⟨1, fun _ => 1, ?_, ?_⟩
  · rw [show d - 1 - (d - 2) = 1 by omega]
    norm_num
  · intro A₀ hA₀
    -- the coefficient scale `b` of the level-`(d-2)` slot coefficients
    set b : ℤ := 2 * |c| * (Nat.factorial d : ℤ) * ((Work.Prop36SW.sSup D d : ℤ) + 1) ^ (d - 2)
      with hbdef
    have hb0 : 0 ≤ b := by rw [hbdef]; positivity
    obtain ⟨Cw, hCw0, hCw1, hw⟩ :=
      entryWindowData D d c A₀ b (1 + 2 * Fintype.card (D.I (d - 1))) hA₀ hd hb0
    set c₀ : ℝ := (((2 : ℝ) ^ (1 + 2 * Fintype.card (D.I (d - 1)))) * (2 * Cw + 1))⁻¹ with hc₀
    have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
    refine ⟨c₀, 1, 1, 1, hc₀0, le_rfl, le_rfl, le_rfl, ?_⟩
    intro N H f η hN hH hf hsu hη0 hη1 hCs hscale hI hfam
    have hH1 : 1 ≤ H := by omega
    obtain ⟨N₀, N₂, hNN₀, hN₀N₂, hH2N₀, hbN₀, hamb, hN₂Cw, hstr⟩ :=
      hw N H η hN hH1 hη0 hη1 hscale
    -- ## elementary window facts
    have hpos : ∀ M : ℕ, (0 : ℝ) < ((symIcc M).card : ℝ) := by
      intro M
      have h : 0 < (symIcc M).card := Finset.card_pos.mpr ⟨0, by simp [Work.Peluse.symIcc]⟩
      exact_mod_cast h
    have hsub : symIcc N ⊆ symIcc N₀ := by
      intro x hx
      rw [Work.Peluse.symIcc, Finset.mem_Icc] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      have hc' : (N : ℤ) ≤ (N₀ : ℤ) := by exact_mod_cast hNN₀
      exact ⟨by omega, by omega⟩
    have hcardle : (symIcc N).card ≤ (symIcc N₀).card := Finset.card_le_card hsub
    set r : ℝ := ((symIcc N).card : ℝ) / ((symIcc N₀).card : ℝ) with hr
    have hr0 : 0 < r := by rw [hr]; exact div_pos (hpos N) (hpos N₀)
    have hrle1 : r ≤ 1 := by
      rw [hr]
      exact div_le_one_of_le₀ (by exact_mod_cast hcardle) (le_of_lt (hpos N₀))
    -- ## the family average, transported to the inflated window `N₀`
    have hfamN₀ : r * η ≤ D.famAvg d H c N₀ f := by
      have h2 : r * D.famAvg d H c N f ≤ D.famAvg d H c N₀ f := by
        rw [hr]
        exact famAvg_window_ratio_le D d H c N N₀ f hNN₀
      have h3 : r * η ≤ r * D.famAvg d H c N f :=
        mul_le_mul_of_nonneg_left hfam (le_of_lt hr0)
      linarith
    have hrη0 : 0 < r * η := mul_pos hr0 hη0
    have hrη1 : r * η ≤ 1 := by
      have h := mul_le_mul hrle1 hη1 (le_of_lt hη0) (by norm_num : (0 : ℝ) ≤ 1)
      simpa using h
    have hN₀1 : 1 ≤ N₀ := le_trans hN hNN₀
    have hI' : 2 ≤ Fintype.card (D.I ((d - 2) + 1)) := by
      rw [show (d - 2) + 1 = d - 1 by omega]
      exact hI
    have hfam' : r * η ≤ D.famAvg ((d - 2) + 2) H c N₀ f := by
      rw [show (d - 2) + 2 = d by omega]
      exact hfamN₀
    -- ## the coefficient hypothesis of `initialStateBox`, with the *correct* bound
    have hbound : ∀ s : D.S ((d - 2) + 1), ∀ a ∈ D.parBox ((d - 2) + 1) H,
        |slotCoeff D ((d - 2) + 2) c (d - 2) s (D.pad ((d - 2) + 1) a)|
            * ((H : ℤ) + 1) * ((H : ℤ) + 1) ≤ (N₀ : ℤ) := by
      intro s a ha
      rw [show (d - 2) + 2 = d by omega]
      have hB := slotCoeffFlatBoundMul D d c H hd s a ha
      have heq : 2 * |c| * (Nat.factorial d : ℤ) * ((Work.Prop36SW.sSup D d : ℤ) + 1) ^ (d - 2)
            * ((H : ℤ) + 1) ^ d = b * ((H : ℤ) + 1) ^ d := by rw [hbdef]
      exact le_trans hB (le_trans (le_of_eq heq) hbN₀)
    have hsuf : SupportIn f N₀ := hsu.mono hNN₀
    -- ## the entry state at the window `N₀`
    have hstate := initialStateBox D (d - 2) c N₀ H f (r * η) hH1 hN₀1 hrη0 hrη1 hf hsuf hI' hfam'
      hbound hH2N₀
    -- ## replacing `|slotCoeff|` by the signed `pFlat` (`pFlat_one` + `LStateBoxAbsIff`)
    have hfun : (fun (s : D.S ((d - 2) + 1)) (x : Fin (nD D ((d - 2) + 1)) → ℤ) =>
          |slotCoeff D ((d - 2) + 2) c (d - 2) s (D.pad ((d - 2) + 1) (decD D ((d - 2) + 1) x))|)
        = (fun (s : D.S ((d - 2) + 1)) (x : Fin (nD D ((d - 2) + 1)) → ℤ) =>
            |pFlat D d c (d - 2) 1 s x|) := by
      funext s x
      rw [show (d - 2) + 2 = d by omega]
      rw [pFlat_one]
    have hstate' : LStateBox (kω := fun _ : SlotSet (D.S ((d - 2) + 1)) (fun _ => 1) => 1)
        (fun (s : D.S ((d - 2) + 1)) (x : Fin (nD D ((d - 2) + 1)) → ℤ) =>
          |pFlat D d c (d - 2) 1 s x|)
        (H + 1) (H + 1) N₀ 1 (Abox D ((d - 2) + 1) H) (fun _ => f)
        (r * η / (2 : ℝ) ^ (1 + 2 * Fintype.card (D.I ((d - 2) + 1)))) := by
      simpa only [hfun] using hstate
    have hLS : LStateBox (kω := fun _ : SlotSet (D.S ((d - 2) + 1)) (fun _ => 1) => 1)
        (pFlat D d c (d - 2) 1) (H + 1) (H + 1) N₀ 1 (Abox D ((d - 2) + 1) H) (fun _ => f)
        (r * η / (2 : ℝ) ^ (1 + 2 * Fintype.card (D.I ((d - 2) + 1)))) :=
      (LStateBoxAbsIff (p := pFlat D d c (d - 2) 1)
        (kω := fun _ : SlotSet (D.S ((d - 2) + 1)) (fun _ => 1) => 1)
        (M₁ := H + 1) (M₂ := H + 1) (N := N₀) (Dc := 1)
        (A := Abox D ((d - 2) + 1) H) (g := fun _ => f)
        (γ := r * η / (2 : ℝ) ^ (1 + 2 * Fintype.card (D.I ((d - 2) + 1))))).mpr hstate'
    -- ## inflating the ambient window to `N₂`
    have hM2 : ((H + 1 : ℕ) : ℝ) * ((H + 1 : ℕ) : ℝ) ≤ (N₂ : ℝ) := by
      have h1 : ((H : ℝ) + 1) * ((H : ℝ) + 1) ≤ (N₀ : ℝ) := hH2N₀
      have h2 : (N₀ : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast hN₀N₂
      push_cast
      linarith
    have hLS2 := LStateBoxMonoAmbient hLS hN₀N₂ hM2
    set γ₂ : ℝ := (r * η / (2 : ℝ) ^ (1 + 2 * Fintype.card (D.I ((d - 2) + 1))))
      * (((symIcc N₀).card : ℝ) / ((symIcc N₂).card : ℝ)) with hγ₂
    have hLS2' : LStateBox (kω := fun _ : SlotSet (D.S ((d - 2) + 1)) (fun _ => 1) => 1)
        (pFlat D d c (d - 2) 1) (H + 1) (H + 1) N₂ 1 (Abox D ((d - 2) + 1) H) (fun _ => f) γ₂ := by
      rw [hγ₂]
      exact hLS2
    -- ## the strength: `c₀ η ≤ γ₂`, from the data-independent window ratio
    have hexp : (1 + 2 * Fintype.card (D.I ((d - 2) + 1))) =
        (1 + 2 * Fintype.card (D.I (d - 1))) := by
      rw [show (d - 2) + 1 = d - 1 by omega]
    have hstr'' : c₀ * η ≤ γ₂ := by
      rw [hγ₂]
      rw [hc₀]
      rw [hr]
      rw [hexp]
      exact hstr
    have hstr' : c₀ * η ^ 1 ≤ γ₂ := by
      rw [pow_one]
      exact hstr''
    refine ⟨H + 1, N₂, γ₂, hLS2', hstr', ?_, ?_, hamb, le_trans hNN₀ hN₀N₂⟩
    · -- `M₁ ≤ (H+1)^{d-1-(d-2)} = H+1`
      have hexp2 : d - 1 - (d - 2) = 1 := by omega
      rw [hexp2]
      simp only [pow_one]
      exact le_of_eq (by push_cast; ring)
    · -- `c₀ η^{e₀} (H+1)^{d-1-(d-2)} ≤ M₁`
      have hexp2 : d - 1 - (d - 2) = 1 := by omega
      rw [hexp2]
      simp only [pow_one]
      have hcη1 : c₀ * η ≤ 1 := le_trans hstr'' hLS2'.2.1
      calc c₀ * η * ((H : ℝ) + 1) ≤ 1 * ((H : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hcη1 (by positivity)
        _ = ((H + 1 : ℕ) : ℝ) := by push_cast; ring

end

end Work.Prop36SW
