/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# A strictly increasing continuous map of `ℝ` above the diagonal is conjugate to a translation

Let `ψ : ℝ → ℝ` be continuous and strictly increasing with `ψ y > y` for every `y`.  This file
proves that there is a strictly increasing `Ψ : ℝ → ℝ` with

  `Ψ (ψ y) = Ψ y + 1`   for all `y`.

No continuity of `Ψ` is required (and none is produced: `Ψ` is a step-like "level function").

## The construction

`ψ` is an orientation preserving self-map of the line which moves every point to its right.  Two
cases occur, and they are genuinely different.

* **`ψ` is surjective.**  Then `ψ` is a homeomorphism of `ℝ` and its orbits are bi-infinite.
  Pick the base point `0` and let `c k = ψ^k 0` (`k ∈ ℤ`) be the orbit of `0`; this is a strictly
  increasing bi-infinite sequence with `c (k+1) = ψ (c k)`, `c k → ±∞`.  Every `y` lies in exactly
  one half-open interval `[c k, c (k+1))`; call its index `lvl y`.  Then `Ψ y = lvl y + P (ψ^{-lvl y} y)`
  where `P` is any strictly increasing map into `(0,1)`.

* **`ψ` is not surjective.**  Then `ψ` has range `(L, ∞)` (the left end `L = sInf (range ψ)` is not
  attained), and the "fundamental domain" is the halfline `(-∞, L]`: every `y` is `ψ^n d` for a
  unique `n : ℕ` and a unique `d ≤ L`.  Hence `ℝ` is, as an ordered set, the lexicographic product
  `ℕ × (-∞, L]`; one may think of `L` as the missing left end and the orbits as one-sided.  Then
  `Ψ y = n + P d` with the same `P`.

In both cases `P : ℝ → (0,1)` strictly increasing (here `P x = (arctan x + π/2)/π`) makes the
"level" part and the "fractional" part fit together: the levels of two points are compared
lexicographically, and the fractional part is strictly increasing inside a level.

## Main statements

* `Work.Implosion.Chord.exists_conj_translation` — the theorem above;
* `Work.Implosion.Chord.exists_conj_translation_of_surjective`,
  `Work.Implosion.Chord.exists_conj_translation_of_not_surjective` — the two cases;
* `Work.Implosion.Chord.conjAux` and its API — the auxiliary strictly increasing map into `(0,1)`.

The orbit lemmas used (`orbit_tendsto_atTop`, `orbit_invFun_tendsto_atBot`, `range_eq_Ioi_sInf`)
live in the sibling files of this directory.
-/
import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Chord.orbit_tendsto_atTop
import Submission.Work.Implosion.Chord.orbit_invFun_tendsto_atBot
import Submission.Work.Implosion.Chord.range_eq_Ioi_sInf

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Chord

/-- The auxiliary strictly increasing map `ℝ → (0,1)` used to compare points inside one
"level" of the conjugacy.  Any strictly increasing map into `(0,1)` would do; this one is
`x ↦ (arctan x + π/2)/π`. -/
noncomputable def conjAux (x : ℝ) : ℝ := (Real.arctan x + Real.pi / 2) / Real.pi

theorem strictMono_conjAux : StrictMono conjAux := by
  intro x y hxy
  rw [conjAux, conjAux]
  exact div_lt_div_of_pos_right (by linarith [Real.arctan_strictMono hxy]) Real.pi_pos

theorem conjAux_pos (x : ℝ) : 0 < conjAux x := by
  rw [conjAux]
  exact div_pos (by linarith [Real.neg_pi_div_two_lt_arctan x]) Real.pi_pos

theorem conjAux_lt_one (x : ℝ) : conjAux x < 1 := by
  rw [conjAux, div_lt_one Real.pi_pos]
  linarith [Real.arctan_lt_pi_div_two x]

/-- On an equivalence `e : ℝ ≃ ℝ` the group power coincides with the iterate of the underlying
function: `(e ^ n) x = e^[n] x`. -/
theorem equivPow_apply (e : ℝ ≃ ℝ) (n : ℕ) (x : ℝ) : (e ^ n) x = e^[n] x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change e ((e ^ n) x) = (⇑e)^[n + 1] x
    rw [ih]
    exact (Function.iterate_succ_apply' (⇑e) n x).symm

/-! ## Case 1: `ψ` is surjective -/

/-- If `ψ : ℝ → ℝ` is continuous, strictly increasing and satisfies `ψ y > y`, and if `ψ` is
surjective, then there is a strictly increasing `Ψ` with `Ψ (ψ y) = Ψ y + 1`.

The proof uses the bi-infinite orbit `k ↦ ψ^k 0` of the base point `0` as a "spine": the index
`lvl y` of the unique interval `[ψ^k 0, ψ^(k+1) 0)` containing `y` is the integer part of `Ψ y`,
and `ψ^{-lvl y} y ∈ [0, ψ 0)` supplies the fractional part. -/
theorem exists_conj_translation_of_surjective (psi : ℝ → ℝ) (hcont : Continuous psi)
    (hmono : StrictMono psi) (hgt : ∀ y : ℝ, y < psi y) (hsurj : Function.Surjective psi) :
    ∃ Psi : ℝ → ℝ, StrictMono Psi ∧ ∀ y : ℝ, Psi (psi y) = Psi y + 1 := by
  classical
  have hinj : Function.Injective psi := hmono.injective
  let e : ℝ ≃ ℝ := Equiv.ofBijective psi ⟨hinj, hsurj⟩
  -- the spine `c : ℤ → ℝ`, `c k = ψ ^ k 0`
  let c : ℤ → ℝ := fun k => (e ^ k) 0
  have hc_succ : ∀ k : ℤ, c (k + 1) = psi (c k) := by
    intro k
    show (e ^ (k + 1)) 0 = psi ((e ^ k) 0)
    rw [show k + 1 = 1 + k by ring, zpow_one_add]
    rfl
  have hc_step : ∀ k : ℤ, c k < c (k + 1) := by
    intro k
    rw [hc_succ k]
    exact hgt (c k)
  have hc_mono : StrictMono c := strictMono_int_of_lt_succ hc_step
  -- the orbit of `0` under `ψ`
  have hc_nat : ∀ n : ℕ, c (n : ℤ) = psi^[n] 0 := by
    intro n
    induction n with
    | zero => simp [c]
    | succ n ih =>
      have h1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [h1, hc_succ, ih, Function.iterate_succ_apply']
  -- the backward orbit of `0`: `c (-n) = ψ ^ (-n) (0) = (ψ⁻¹)^[n] 0`
  have hesymm_mono : StrictMono (fun y : ℝ => e.symm y) := by
    intro x y hxy
    by_contra hcon
    change ¬ e.symm x < e.symm y at hcon
    have hcon' : e.symm y ≤ e.symm x := not_lt.mp hcon
    have h1 : y ≤ x := by
      calc y = e (e.symm y) := (Equiv.apply_symm_apply e y).symm
        _ ≤ e (e.symm x) := hmono.monotone hcon'
        _ = x := Equiv.apply_symm_apply e x
    exact absurd h1 (not_le.mpr hxy)
  have hc_neg : ∀ n : ℕ, c (-(n : ℤ)) = (e.symm^[n]) 0 := by
    intro n
    induction n with
    | zero => simp [c]
    | succ n ih =>
      have h1 : (-((n + 1 : ℕ) : ℤ)) = (-(n : ℤ)) - 1 := by push_cast; ring
      rw [h1]
      have h2 : c (-(n : ℤ)) = psi (c (-(n : ℤ) - 1)) := by
        have h := hc_succ (-(n : ℤ) - 1)
        rwa [sub_add_cancel] at h
      have h3 : c (-(n : ℤ) - 1) = e.symm (c (-(n : ℤ))) := by
        have h4 : e (c (-(n : ℤ) - 1)) = c (-(n : ℤ)) := h2.symm
        rw [← h4, Equiv.symm_apply_apply]
      rw [h3, ih]
      exact (Function.iterate_succ_apply' (⇑e.symm) n 0).symm
  -- `Function.invFun ψ` is the inverse of `ψ`, i.e. `e.symm`
  have hfun : Function.invFun psi = ⇑e.symm := by
    funext y
    apply hinj
    rw [Function.invFun_eq (hsurj y)]
    exact (Equiv.apply_symm_apply e y).symm
  -- the spine is unbounded below
  have hback : ∀ y : ℝ, ∃ k : ℤ, c k ≤ y := by
    intro y
    have h := orbit_invFun_tendsto_atBot psi hcont hmono hgt hsurj 0
    rw [Filter.tendsto_atTop_atBot] at h
    obtain ⟨n, hn⟩ := h y
    refine ⟨-(n : ℤ), ?_⟩
    rw [hc_neg n]
    simpa [hfun] using hn n le_rfl
  -- the spine is unbounded above
  have hex : ∀ y : ℝ, ∃ k : ℤ, y < c (k + 1) := by
    intro y
    have h := orbit_tendsto_atTop psi hcont hmono hgt 0
    rw [Filter.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h y)
    refine ⟨(N : ℤ), ?_⟩
    have h2 : ((N : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h2]
    calc y ≤ psi^[N] 0 := hN N le_rfl
      _ = c (N : ℤ) := (hc_nat N).symm
      _ < c ((N : ℤ) + 1) := hc_step (N : ℤ)
      _ = c ((N + 1 : ℕ) : ℤ) := by rw [h2]
  -- the level of a point: the least `k` with `y < c (k+1)`
  let klo : ℝ → ℤ := fun y => Classical.choose (hback y)
  have hklo_spec : ∀ y : ℝ, c (klo y) ≤ y := fun y => Classical.choose_spec (hback y)
  let lvl : ℝ → ℤ := fun y =>
    (Int.leastOfBdd (P := fun k : ℤ => y < c (k + 1)) (klo y)
      (fun z hz => by
        by_contra hcon
        rw [not_le] at hcon
        have h1 : c (z + 1) ≤ c (klo y) := hc_mono.monotone (by omega)
        linarith [hklo_spec y, h1])
      (hex y) : ℤ)
  have hleast : ∀ y : ℝ, IsLeast {k : ℤ | y < c (k + 1)} (lvl y) := by
    intro y
    exact Int.isLeast_coe_leastOfBdd _ _ _
  have hlvl_lt : ∀ y : ℝ, y < c (lvl y + 1) := fun y => (hleast y).1
  have hlvl_le : ∀ y : ℝ, c (lvl y) ≤ y := by
    intro y
    by_contra hcon
    rw [not_le] at hcon
    have hmem : (lvl y - 1) ∈ {k : ℤ | y < c (k + 1)} := by
      show y < c ((lvl y - 1) + 1)
      rw [sub_add_cancel]
      exact hcon
    have := (hleast y).2 hmem
    omega
  have hlvl_eq_of : ∀ (k : ℤ) (z : ℝ), c k ≤ z → z < c (k + 1) → lvl z = k := by
    intro k z h1 h2
    have hle : lvl z ≤ k := (hleast z).2 h2
    have hge : k ≤ lvl z := by
      by_contra hcon
      rw [not_le] at hcon
      have h3 : c (lvl z + 1) ≤ c k := hc_mono.monotone (by omega)
      linarith [hlvl_lt z]
    omega
  -- the group power of `e` is strictly increasing, for every integer exponent
  have hzpow_mono : ∀ j : ℤ, StrictMono (fun y : ℝ => (e ^ j) y) := by
    intro j
    by_cases hj : 0 ≤ j
    · have hje : (e ^ j : ℝ ≃ ℝ) = (e ^ j.toNat : ℝ ≃ ℝ) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hj]
      have h2 : (fun y : ℝ => (e ^ j) y) = (⇑e)^[j.toNat] := by
        funext y
        rw [hje]
        exact equivPow_apply e j.toNat y
      rw [h2]
      exact hmono.iterate j.toNat
    · have hje : (e ^ j : ℝ ≃ ℝ) = (e.symm ^ (-j)) := by
        have h1 : (e⁻¹ : ℝ ≃ ℝ) ^ (-j) = e ^ j := by rw [inv_zpow, zpow_neg, inv_inv]
        rw [← h1, Equiv.Perm.inv_def]
      have h2 : (fun y : ℝ => (e ^ j) y) = (⇑e.symm)^[(-j).toNat] := by
        funext y
        rw [hje]
        have h3 : (-j : ℤ) = (((-j).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
        rw [h3, zpow_natCast]
        exact equivPow_apply (e.symm) (-j).toNat y
      rw [h2]
      exact hesymm_mono.iterate (-j).toNat
  -- the coordinate of `y` inside its level: `ψ ^ (-lvl y) y`
  let tr : ℤ → ℝ → ℝ := fun k y => (e ^ (-k)) y
  have htr_succ : ∀ (k : ℤ) (y : ℝ), tr (k + 1) (psi y) = tr k y := by
    intro k y
    show (e ^ (-(k + 1))) (e y) = (e ^ (-k)) y
    have h2 : (e ^ (-(k + 1))) * e = e ^ (-k) := by
      rw [← zpow_add_one]
      congr 1
      ring
    change ((e ^ (-(k + 1))) * e) y = (e ^ (-k)) y
    rw [h2]
  let Psi : ℝ → ℝ := fun y => (lvl y : ℝ) + conjAux (tr (lvl y) y)
  refine ⟨Psi, ?_, ?_⟩
  · intro y1 y2 hy
    have hlev : lvl y1 ≤ lvl y2 := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : c (lvl y2 + 1) ≤ c (lvl y1) := hc_mono.monotone (by omega)
      linarith [hlvl_le y1, hlvl_lt y2]
    rcases lt_or_eq_of_le hlev with hlt | heq
    · have h1 : (lvl y1 : ℝ) + conjAux (tr (lvl y1) y1) < (lvl y1 : ℝ) + 1 := by
        linarith [conjAux_lt_one (tr (lvl y1) y1)]
      have h2 : (lvl y2 : ℝ) < (lvl y2 : ℝ) + conjAux (tr (lvl y2) y2) := by
        linarith [conjAux_pos (tr (lvl y2) y2)]
      have h3 : (lvl y1 : ℝ) + 1 ≤ (lvl y2 : ℝ) := by exact_mod_cast hlt
      show (lvl y1 : ℝ) + conjAux (tr (lvl y1) y1)
          < (lvl y2 : ℝ) + conjAux (tr (lvl y2) y2)
      linarith
    · have h1 : tr (lvl y1) y1 < tr (lvl y1) y2 := hzpow_mono (-lvl y1) hy
      have h2 := strictMono_conjAux h1
      show (lvl y1 : ℝ) + conjAux (tr (lvl y1) y1)
          < (lvl y2 : ℝ) + conjAux (tr (lvl y2) y2)
      rw [← heq]
      linarith
  · intro y
    have hshift : lvl (psi y) = lvl y + 1 := by
      have hle : c (lvl y + 1) ≤ psi y := by
        rw [hc_succ (lvl y)]
        exact hmono.monotone (hlvl_le y)
      have hlt : psi y < c ((lvl y + 1) + 1) := by
        have h2 : c ((lvl y + 1) + 1) = psi (c (lvl y + 1)) := hc_succ (lvl y + 1)
        rw [h2]
        exact hmono (hlvl_lt y)
      exact hlvl_eq_of (lvl y + 1) (psi y) hle (by rwa [add_assoc] at hlt ⊢)
    show (lvl (psi y) : ℝ) + conjAux (tr (lvl (psi y)) (psi y))
        = (lvl y : ℝ) + conjAux (tr (lvl y) y) + 1
    rw [hshift, htr_succ (lvl y) y]
    push_cast
    ring

/-! ## Case 2: `ψ` is not surjective -/

/-- If `ψ : ℝ → ℝ` is continuous, strictly increasing and satisfies `ψ y > y`, and if `ψ` is
*not* surjective, then there is a strictly increasing `Ψ` with `Ψ (ψ y) = Ψ y + 1`.

Here `range ψ = (L, ∞)` with `L = sInf (range ψ)`, the halfline `(-∞, L]` is a fundamental domain,
and the spine `n ↦ ψ^n L` gives the level of every point; the coordinate is the `ψ^n`-preimage of
`y`, which always lies in `(-∞, L]`. -/
theorem exists_conj_translation_of_not_surjective (psi : ℝ → ℝ) (hcont : Continuous psi)
    (hmono : StrictMono psi) (hgt : ∀ y : ℝ, y < psi y) (hnot : ¬ Function.Surjective psi) :
    ∃ Psi : ℝ → ℝ, StrictMono Psi ∧ ∀ y : ℝ, Psi (psi y) = Psi y + 1 := by
  classical
  have hrange : Set.range psi = Set.Ioi (sInf (Set.range psi)) :=
    range_eq_Ioi_sInf psi hcont hmono hgt hnot
  let L : ℝ := sInf (Set.range psi)
  have hLlt : ∀ y : ℝ, L < psi y := by
    intro y
    have : psi y ∈ Set.Ioi L := by rw [← hrange]; exact Set.mem_range_self y
    exact this
  -- `ψ` maps each halfline `Ioi x` onto `Ioi (ψ x)`
  have himage : ∀ x : ℝ, psi '' Set.Ioi x = Set.Ioi (psi x) := by
    intro x
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hmono hw
    · intro hy
      have hyrange : y ∈ Set.range psi := by rw [hrange]; exact lt_trans (hLlt x) hy
      obtain ⟨w, hw⟩ := hyrange
      refine ⟨w, ?_, hw⟩
      by_contra hcon
      rw [Set.mem_Ioi, not_lt] at hcon
      have h2 : psi w ≤ psi x := hmono.monotone hcon
      rw [hw] at h2
      have hy' : psi x < y := hy
      linarith
  -- the spine `n ↦ ψ^n L`
  let bn : ℕ → ℝ := fun n => psi^[n] L
  have hbn_succ : ∀ n : ℕ, bn (n + 1) = psi (bn n) := fun n =>
    Function.iterate_succ_apply' psi n L
  have hbn_lt : ∀ n : ℕ, bn n < bn (n + 1) := by
    intro n
    rw [hbn_succ n]
    exact hgt (bn n)
  have hbn_mono : StrictMono bn := strictMono_nat_of_lt_succ hbn_lt
  -- the range of `ψ ^ (n+1)` is `Ioi (bn n)`
  have hrange_iter : ∀ n : ℕ, Set.range (psi^[n+1]) = Set.Ioi (bn n) := by
    intro n
    induction n with
    | zero => simpa [bn, L] using hrange
    | succ k ih =>
      have h1 : psi^[k+2] = psi ∘ psi^[k+1] := by
        funext x
        exact Function.iterate_succ_apply' psi (k+1) x
      rw [h1, Set.range_comp, ih, himage]
      congr 1
      exact (hbn_succ k).symm
  -- the level of a point
  have hnlvl_ex : ∀ y : ℝ, ∃ n : ℕ, y ≤ bn n := by
    intro y
    have h := orbit_tendsto_atTop psi hcont hmono hgt L
    rw [Filter.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h y)
    exact ⟨N, hN N le_rfl⟩
  let nlvl : ℝ → ℕ := fun y => Nat.find (hnlvl_ex y)
  have hnlvl_spec : ∀ y : ℝ, y ≤ bn (nlvl y) := fun y => Nat.find_spec (hnlvl_ex y)
  have hnlvl_min : ∀ (y : ℝ) (m : ℕ), m < nlvl y → bn m < y := by
    intro y m hm
    by_contra hc
    rw [not_lt] at hc
    have h1 : nlvl y ≤ m := Nat.find_min' (hnlvl_ex y) hc
    omega
  have hnlvl_eq_of : ∀ (n : ℕ) (z : ℝ), z ≤ bn n → (∀ m : ℕ, m < n → ¬ (z ≤ bn m)) →
      nlvl z = n := by
    intro n z h1 h2
    show Nat.find (hnlvl_ex z) = n
    exact (Nat.find_eq_iff (hnlvl_ex z)).mpr ⟨h1, h2⟩
  -- the level increases by one under `ψ`
  have hshift : ∀ y : ℝ, nlvl (psi y) = nlvl y + 1 := by
    intro y
    apply hnlvl_eq_of
    · rw [hbn_succ (nlvl y)]
      exact hmono.monotone (hnlvl_spec y)
    · intro m hm
      rw [not_le]
      have hm' : m ≤ nlvl y := Nat.lt_succ_iff.mp hm
      rcases lt_or_eq_of_le hm' with hlt | heq
      · exact lt_trans (hnlvl_min y m hlt) (hgt y)
      · rw [heq]
        rcases Nat.eq_zero_or_pos (nlvl y) with h0 | hpos
        · rw [h0]
          exact hLlt y
        · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
          rw [hk, hbn_succ k]
          exact hmono (hnlvl_min y k (by omega))
  -- the coordinate of `y`: its `ψ ^ (nlvl y)`-preimage, which lies in `(-∞, L]`
  let d : ℝ → ℝ := fun y => Function.invFun (psi^[nlvl y]) y
  have hd_spec : ∀ y : ℝ, psi^[nlvl y] (d y) = y := by
    intro y
    apply Function.invFun_eq
    rcases Nat.eq_zero_or_pos (nlvl y) with h0 | hpos
    · rw [h0]
      exact ⟨y, rfl⟩
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      rw [hk]
      have hy : y ∈ Set.Ioi (bn k) := Set.mem_Ioi.mpr (hnlvl_min y k (by omega))
      have hy' : y ∈ Set.range (psi^[k+1]) := by rwa [hrange_iter k]
      exact hy'
  have hd_le : ∀ y : ℝ, d y ≤ L := by
    intro y
    rcases Nat.eq_zero_or_pos (nlvl y) with h0 | hpos
    · have h1 : d y = y := by
        show Function.invFun (psi^[nlvl y]) y = y
        rw [h0]
        exact Function.leftInverse_invFun (f := id) Function.injective_id y
      rw [h1]
      have h2 : y ≤ bn 0 := by rw [← h0]; exact hnlvl_spec y
      have h3 : bn 0 = L := rfl
      rw [h3] at h2
      exact h2
    · by_contra hcon
      rw [not_le] at hcon
      have h1 : psi^[nlvl y] L < psi^[nlvl y] (d y) := (hmono.iterate (nlvl y)) hcon
      rw [hd_spec y] at h1
      have h2 : bn (nlvl y) = psi^[nlvl y] L := rfl
      have h3 := hnlvl_spec y
      rw [h2] at h3
      linarith
  have hd_mono : ∀ y1 y2 : ℝ, nlvl y1 = nlvl y2 → y1 < y2 → d y1 < d y2 := by
    intro y1 y2 heq hlt
    by_contra hcon
    rw [not_lt] at hcon
    have h3 : psi^[nlvl y1] (d y2) ≤ psi^[nlvl y1] (d y1) := by
      have h : psi^[nlvl y2] (d y2) ≤ psi^[nlvl y2] (d y1) :=
        (hmono.iterate (nlvl y2)).monotone hcon
      rwa [← heq] at h
    have h4 : psi^[nlvl y1] (d y2) = y2 := by rw [heq]; exact hd_spec y2
    have h5 : psi^[nlvl y1] (d y1) = y1 := hd_spec y1
    rw [h4, h5] at h3
    linarith
  let Psi : ℝ → ℝ := fun y => (nlvl y : ℝ) + conjAux (d y)
  refine ⟨Psi, ?_, ?_⟩
  · intro y1 y2 hy
    have hlev : nlvl y1 ≤ nlvl y2 := by
      show Nat.find (hnlvl_ex y1) ≤ Nat.find (hnlvl_ex y2)
      exact Nat.find_min' (hnlvl_ex y1) (le_trans (le_of_lt hy) (hnlvl_spec y2))
    rcases lt_or_eq_of_le hlev with hlt | heq
    · have h1 : (nlvl y1 : ℝ) + conjAux (d y1) < (nlvl y1 : ℝ) + 1 := by
        linarith [conjAux_lt_one (d y1)]
      have h2 : (nlvl y2 : ℝ) < (nlvl y2 : ℝ) + conjAux (d y2) := by
        linarith [conjAux_pos (d y2)]
      have h3 : (nlvl y1 : ℝ) + 1 ≤ (nlvl y2 : ℝ) := by exact_mod_cast hlt
      show (nlvl y1 : ℝ) + conjAux (d y1) < (nlvl y2 : ℝ) + conjAux (d y2)
      linarith
    · have h1 : d y1 < d y2 := hd_mono y1 y2 heq hy
      have h2 := strictMono_conjAux h1
      show (nlvl y1 : ℝ) + conjAux (d y1) < (nlvl y2 : ℝ) + conjAux (d y2)
      rw [← heq]
      linarith
  · intro y
    have hd_eq : d (psi y) = d y := by
      show Function.invFun (psi^[nlvl (psi y)]) (psi y) = Function.invFun (psi^[nlvl y]) y
      rw [hshift]
      have hψ : psi^[nlvl y + 1] (d y) = psi y := by
        rw [Function.iterate_succ_apply' psi (nlvl y) (d y), hd_spec y]
      have h1 : Function.invFun (psi^[nlvl y + 1]) (psi^[nlvl y + 1] (d y)) = d y :=
        Function.leftInverse_invFun (hmono.iterate (nlvl y + 1)).injective (d y)
      have h2 : Function.invFun (psi^[nlvl y]) (psi^[nlvl y] (d y)) = d y :=
        Function.leftInverse_invFun (hmono.iterate (nlvl y)).injective (d y)
      calc Function.invFun (psi^[nlvl y + 1]) (psi y)
          = Function.invFun (psi^[nlvl y + 1]) (psi^[nlvl y + 1] (d y)) := by rw [hψ]
        _ = d y := h1
        _ = Function.invFun (psi^[nlvl y]) (psi^[nlvl y] (d y)) := h2.symm
        _ = Function.invFun (psi^[nlvl y]) y := by rw [hd_spec y]
    show (nlvl (psi y) : ℝ) + conjAux (d (psi y)) = (nlvl y : ℝ) + conjAux (d y) + 1
    rw [hshift, hd_eq]
    push_cast
    ring

/-! ## The theorem -/

theorem exists_conj_translation (psi : ℝ → ℝ) (hcont : Continuous psi) (hmono : StrictMono psi)
    (hgt : ∀ y : ℝ, y < psi y) :
    ∃ Psi : ℝ → ℝ, StrictMono Psi ∧ ∀ y : ℝ, Psi (psi y) = Psi y + 1 := by
  by_cases hsurj : Function.Surjective psi
  · exact exists_conj_translation_of_surjective psi hcont hmono hgt hsurj
  · exact exists_conj_translation_of_not_surjective psi hcont hmono hgt hsurj

end Work.Implosion.Chord
