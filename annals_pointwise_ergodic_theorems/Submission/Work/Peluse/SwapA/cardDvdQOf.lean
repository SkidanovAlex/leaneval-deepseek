import Mathlib
import Submission.Work.Peluse.SwapA.genDefs

/-!
# The divisor count for the regime-swap slopes

The slope attached to a plug `v = (h,h') ∈ [H]^t × [H]^t` and a sign pattern `ω : Fin t → Bool`
is `qOf ω v = ω·(h − h') = linForm ω h − linForm ω h'`.  This module proves that for a *nonzero*
pattern the number of plugs with `d ∣ qOf ω v` is at most `(1/d + 1/H)·H^(2t)`.

The argument is the "one live coordinate" count: fix the live coordinate `i₀` (where `ω i₀ = true`)
and all the other coordinates of `h` together with all of `h'`; the divisibility condition then
places `h i₀` in a single residue class modulo `d`, of which there are at most `H/d + 1` in `[H]`.
Summing over the `H^t · H^(t-1)` freed choices gives the claim.  The three ingredients are
`restK` (the linear form with the live coordinate removed, as a function of the remaining values),
`linForm_eq_coord_add` (the exact decomposition of `linForm`), and the fibre bound
`fiber_card_le` (one residue class count, via `card_fin_mod_le` of `genDefs`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.SwapA

noncomputable section

/-- The part of `linForm ω` carried by the coordinates other than `i₀`, read off from the values
`b` of a shift tuple off `i₀`. -/
def restK {t H : ℕ} (ω : Fin t → Bool) (i₀ : Fin t) (b : {i : Fin t // i ≠ i₀} → Fin H) : ℤ :=
  ∑ j : {i : Fin t // i ≠ i₀}, (if ω j.1 then ((b j : ℤ)) else 0)

/-- A sum over the complement subtype is a sum over the erased finset. -/
lemma sum_subtype_eq_sum_erase {t : ℕ} (i₀ : Fin t) (f : Fin t → ℤ) :
    (∑ j : {i : Fin t // i ≠ i₀}, f j.1) = ∑ i ∈ Finset.univ.erase i₀, f i := by
  rw [← Finset.filter_ne' (Finset.univ : Finset (Fin t)) i₀]
  rw [← Finset.sum_subtype_eq_sum_filter (p := fun i : Fin t => i ≠ i₀) f]
  rw [Finset.subtype_univ]

/-- The linear form splits off a live coordinate. -/
lemma linForm_eq_coord_add {t H : ℕ} (ω : Fin t → Bool) {i₀ : Fin t} (hi₀ : ω i₀ = true)
    (h : Fin t → Fin H) :
    linForm ω h = (h i₀ : ℤ)
      + ∑ j : {i : Fin t // i ≠ i₀}, (if ω j.1 then ((h j.1 : ℤ)) else 0) := by
  have h1 : linForm ω h = (h i₀ : ℤ)
      + ∑ i ∈ Finset.univ.erase i₀, (if ω i then (h i : ℤ) else 0) := by
    rw [linForm, ← Finset.sum_erase_add (Finset.univ : Finset (Fin t))
      (fun i => if ω i then (h i : ℤ) else 0) (Finset.mem_univ i₀), hi₀, if_pos rfl]
    ring
  rw [h1, ← sum_subtype_eq_sum_erase i₀ (fun i => if ω i then (h i : ℤ) else 0)]

/-- The linear form splits off a live coordinate, with the remaining part computed from the values
off `i₀` only (`restK`). -/
lemma linForm_eq_coord_add_of_eq {t H : ℕ} (ω : Fin t → Bool) {i₀ : Fin t} (hi₀ : ω i₀ = true)
    (h : Fin t → Fin H) (b : {i : Fin t // i ≠ i₀} → Fin H)
    (hb : (fun j : {i : Fin t // i ≠ i₀} => h j.1) = b) :
    linForm ω h = (h i₀ : ℤ) + restK ω i₀ b := by
  rw [linForm_eq_coord_add ω hi₀ h, restK]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show h j.1 = b j from congrFun hb j]

/-- **One fibre.**  Fixing both entries of `h'` and all entries of `h` off a live coordinate `i₀`,
at most `H/d + 1` values of that coordinate keep the divisibility `d ∣ qOf ω v`: the condition
places it in a single residue class modulo `d`. -/
lemma fiber_card_le {t H d : ℕ} (hd : 1 ≤ d) (ω : Fin t → Bool) {i₀ : Fin t} (hi₀ : ω i₀ = true)
    (S : Finset (Plug t H)) (hS : ∀ v ∈ S, (d : ℤ) ∣ qOf ω v)
    (h' : Fin t → Fin H) (b : {i : Fin t // i ≠ i₀} → Fin H) :
    ((S.filter (fun v : Plug t H => v.2 = h' ∧
        (fun j : {i : Fin t // i ≠ i₀} => v.1 j.1) = b)).card : ℝ)
      ≤ (H : ℝ) / (d : ℝ) + 1 := by
  classical
  set k : ℤ := linForm ω h' - restK ω i₀ b with hk
  set F : Finset (Plug t H) := S.filter (fun v => v.2 = h' ∧
      (fun j : {i : Fin t // i ≠ i₀} => v.1 j.1) = b) with hF
  set U : Finset (Fin H) := Finset.univ.filter (fun x : Fin H => (d : ℤ) ∣ ((x : ℤ) - k)) with hU
  have hmaps : Set.MapsTo (fun v : Plug t H => v.1 i₀) ↑F ↑U := by
    intro v hv
    rw [hF, Finset.mem_coe, Finset.mem_filter] at hv
    obtain ⟨hvS, hv2, hvb⟩ := hv
    simp only [hU, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : qOf ω v = (v.1 i₀ : ℤ) + restK ω i₀ b - linForm ω h' := by
      rw [qOf_eq_linForm, hv2, linForm_eq_coord_add_of_eq ω hi₀ v.1 b hvb]
    have hthis := hS v hvS
    rw [h1] at hthis
    have hgoal : (v.1 i₀ : ℤ) + restK ω i₀ b - linForm ω h' = (v.1 i₀ : ℤ) - k := by
      rw [hk]; ring
    rwa [hgoal] at hthis
  have hinj : Set.InjOn (fun v : Plug t H => v.1 i₀) ↑F := by
    intro v hv w hw heq
    rw [hF, Finset.mem_coe, Finset.mem_filter] at hv hw
    obtain ⟨-, hv2, hvb⟩ := hv
    obtain ⟨-, hw2, hwb⟩ := hw
    have hfun : v.1 = w.1 := by
      funext i
      by_cases hi : i = i₀
      · rw [hi]; exact heq
      · have e1 : v.1 i = b ⟨i, hi⟩ := by
          have := congrFun hvb ⟨i, hi⟩; simpa using this
        have e2 : w.1 i = b ⟨i, hi⟩ := by
          have := congrFun hwb ⟨i, hi⟩; simpa using this
        rw [e1, e2]
    exact Prod.ext hfun (hv2.trans hw2.symm)
  calc (F.card : ℝ) ≤ (U.card : ℝ) := by
        exact_mod_cast Finset.card_le_card_of_injOn (fun v : Plug t H => v.1 i₀) hmaps hinj
    _ ≤ (H : ℝ) / (d : ℝ) + 1 := card_fin_mod_le hd k

/-- **(divisor count)** For a nonzero sign pattern `ω` and `d ≥ 1`, the number of plugs
`v = (h,h') ∈ [H]^t × [H]^t` with `d ∣ ω·(h−h')` is at most `(1/d + 1/H)·H^(2t)`.
Useful helper in `Submission.Work.Peluse.SwapA.genDefs`: `card_fin_mod_le`
(`#{x : Fin H : d ∣ (x − k)} ≤ H/d + 1`) and `linForm_update_inj`. -/
theorem cardDvdQOf {t H d : ℕ} (ht : 1 ≤ t) (hH : 1 ≤ H) (hd : 1 ≤ d)
    (ω : Fin t → Bool) (hω : ω ≠ 0) :
    ((Finset.univ.filter (fun v : Work.Peluse.SwapA.Plug t H =>
        (d : ℤ) ∣ Work.Peluse.SwapA.qOf ω v)).card : ℝ)
      ≤ (1 / (d : ℝ) + 1 / (H : ℝ)) * (Fintype.card (Work.Peluse.SwapA.Plug t H) : ℝ) := by
  classical
  -- A live coordinate of the pattern, and the key that frees the live coordinate of `h`.
  obtain ⟨i₀, hi₀⟩ := exists_true_of_ne_zero hω
  set S : Finset (Plug t H) := Finset.univ.filter (fun v => (d : ℤ) ∣ qOf ω v) with hS
  set key : Plug t H → (Fin t → Fin H) × ({i : Fin t // i ≠ i₀} → Fin H) :=
    fun v => (v.2, fun j => v.1 j.1) with hkey
  -- Fibre the count over the key: each `h'` and each choice off `i₀` of `h` is one fibre.
  have hcard_eq : (S.card : ℝ)
      = ∑ b ∈ S.image key, ((S.filter (fun v => key v = b)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image key S
  have hfiber : ∀ b ∈ S.image key,
      ((S.filter (fun v => key v = b)).card : ℝ) ≤ (H : ℝ) / (d : ℝ) + 1 := by
    intro b _
    obtain ⟨h', bb⟩ := b
    have hsub : S.filter (fun v => key v = (h', bb))
        = S.filter (fun v => v.2 = h' ∧
            (fun j : {i : Fin t // i ≠ i₀} => v.1 j.1) = bb) := by
      apply Finset.filter_congr
      intro v _
      simp only [hkey, Prod.mk.injEq]
    rw [hsub]
    refine fiber_card_le hd ω hi₀ S ?_ h' bb
    intro v hv
    have hv' := hv
    rw [hS] at hv'
    exact (Finset.mem_filter.mp hv').2
  have hstep : (S.card : ℝ) ≤ ∑ b ∈ S.image key, ((H : ℝ) / (d : ℝ) + 1) := by
    rw [hcard_eq]
    exact Finset.sum_le_sum hfiber
  have hsum : (∑ b ∈ S.image key, ((H : ℝ) / (d : ℝ) + 1))
      = ((S.image key).card : ℝ) * ((H : ℝ) / (d : ℝ) + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  -- The key takes at most `H^t · H^(t-1)` values.
  have himg : ((S.image key).card : ℝ) ≤ (H : ℝ) ^ t * (H : ℝ) ^ (t - 1) := by
    have hc : Fintype.card {i : Fin t // i ≠ i₀} = t - 1 := by
      rw [Fintype.card_subtype_compl (fun i : Fin t => i = i₀)]
      simp [Fintype.card_fin]
    have hcard : (S.image key).card ≤ H ^ t * H ^ (t - 1) := by
      calc (S.image key).card
          ≤ Fintype.card ((Fin t → Fin H) × ({i : Fin t // i ≠ i₀} → Fin H)) :=
            Finset.card_le_univ _
        _ = H ^ t * H ^ (t - 1) := by
            simp [Fintype.card_prod, Fintype.card_fin, hc]
    exact_mod_cast hcard
  -- The endgame: `(H^t)·(H^(t-1))·(H/d + 1) = (1/d + 1/H)·H^t·H^t`.
  have hfinal : (H : ℝ) ^ t * ((H : ℝ) ^ (t - 1) * ((H : ℝ) / (d : ℝ) + 1))
      = (1 / (d : ℝ) + 1 / (H : ℝ)) * ((H : ℝ) ^ t * (H : ℝ) ^ t) := by
    have hsplit : (H : ℝ) ^ t = (H : ℝ) ^ (t - 1) * H := by
      rw [← pow_succ, Nat.sub_add_cancel ht]
    have hd0 : (d : ℝ) ≠ 0 := by
      have : d ≠ 0 := by omega
      exact_mod_cast this
    have hH0 : (H : ℝ) ≠ 0 := by
      have : H ≠ 0 := by omega
      exact_mod_cast this
    rw [hsplit]
    field_simp
  have hplug : (Fintype.card (Plug t H) : ℝ) = (H : ℝ) ^ t * (H : ℝ) ^ t := by
    simp [Plug, Fintype.card_prod, Fintype.card_fin]
  calc ((Finset.univ.filter (fun v : Plug t H => (d : ℤ) ∣ qOf ω v)).card : ℝ)
      = (S.card : ℝ) := by rw [hS]
    _ ≤ ∑ b ∈ S.image key, ((H : ℝ) / (d : ℝ) + 1) := hstep
    _ = ((S.image key).card : ℝ) * ((H : ℝ) / (d : ℝ) + 1) := hsum
    _ ≤ ((H : ℝ) ^ t * (H : ℝ) ^ (t - 1)) * ((H : ℝ) / (d : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right himg (by positivity)
    _ = (1 / (d : ℝ) + 1 / (H : ℝ)) * (Fintype.card (Plug t H) : ℝ) := by
        rw [hplug, ← hfinal]
        ring

end

end Work.Peluse.SwapA
