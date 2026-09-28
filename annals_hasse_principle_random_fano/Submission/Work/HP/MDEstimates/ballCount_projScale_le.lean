import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.numaux.ker_projScale_inf
import Submission.Work.HP.MDEstimates.eNorm_sub_le

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP.MDEstimates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite set of integers, pairwise separated by `s` and of diameter at most `R`, has at most
`R/s + 1` elements. -/
lemma card_le_of_separated {A : Finset ℤ} {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → s ≤ |(a:ℝ) - (b:ℝ)|)
    (hbd : ∀ a ∈ A, ∀ b ∈ A, |(a:ℝ) - (b:ℝ)| ≤ R) :
    (A.card : ℝ) ≤ R / s + 1 := by
  by_cases h1 : A.card ≤ 1
  · have hc : (A.card : ℝ) ≤ 1 := by exact_mod_cast h1
    have h0 : 0 ≤ R / s := div_nonneg hR hs.le
    linarith
  · push Not at h1
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    set m : ℤ := A.min' hne with hm
    have hmem : m ∈ A := A.min'_mem hne
    have hle : ∀ a ∈ A, m ≤ a := fun a ha => A.min'_le a ha
    let g : ℤ → ℕ := fun a => ⌊((a - m : ℤ) : ℝ) / s⌋₊
    have hnonneg : ∀ a ∈ A, (0:ℝ) ≤ ((a - m : ℤ) : ℝ) := by
      intro a ha
      have : (0:ℤ) ≤ a - m := by have := hle a ha; omega
      exact_mod_cast this
    have hmono : ∀ a ∈ A, ∀ b ∈ A, a < b → g a < g b := by
      intro a ha b hb hab
      have hsep' : s ≤ ((b - a : ℤ) : ℝ) := by
        have h := hsep a ha b hb (ne_of_lt hab)
        have hle' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab.le
        rw [abs_sub_comm, abs_of_nonneg (by linarith)] at h
        have hcast : ((b - a : ℤ) : ℝ) = (b:ℝ) - (a:ℝ) := by push_cast; ring
        linarith
      have hstep : ((a - m : ℤ) : ℝ) / s + 1 ≤ ((b - m : ℤ) : ℝ) / s := by
        have h2 : 1 ≤ ((b - a : ℤ) : ℝ) / s := by rw [le_div_iff₀ hs]; linarith
        have h3 : ((a - m : ℤ) : ℝ) / s + ((b - a : ℤ) : ℝ) / s = ((b - m : ℤ) : ℝ) / s := by
          rw [← add_div]; congr 1; push_cast; ring
        linarith
      show ⌊((a - m : ℤ) : ℝ) / s⌋₊ < ⌊((b - m : ℤ) : ℝ) / s⌋₊
      have hx0 : (0:ℝ) ≤ ((a - m : ℤ) : ℝ) / s := div_nonneg (hnonneg a ha) hs.le
      have := Nat.floor_mono hstep
      rw [Nat.floor_add_one hx0] at this
      omega
    have hginj : Set.InjOn g ↑A := by
      intro a ha b hb h
      rcases lt_trichotomy a b with hlt | heq | hgt
      · exact absurd h (ne_of_lt (hmono a ha b hb hlt))
      · exact heq
      · exact absurd h.symm (ne_of_lt (hmono b hb a ha hgt))
    have hcard : (A.image g).card = A.card := Finset.card_image_of_injOn hginj
    have hbound : ∀ a ∈ A, g a < ⌊R / s⌋₊ + 1 := by
      intro a ha
      have h1 : ((a - m : ℤ) : ℝ) ≤ R := by
        have habs := hbd a ha m hmem
        have hcast : ((a - m : ℤ) : ℝ) = (a:ℝ) - (m:ℝ) := by push_cast; ring
        rw [← hcast, abs_of_nonneg (hnonneg a ha)] at habs
        exact habs
      have h2 : ⌊((a - m : ℤ) : ℝ) / s⌋₊ ≤ ⌊R / s⌋₊ :=
        Nat.floor_mono (div_le_div_of_nonneg_right h1 hs.le)
      change ⌊((a - m : ℤ) : ℝ) / s⌋₊ < ⌊R / s⌋₊ + 1
      omega
    have hsub : A.image g ⊆ Finset.range (⌊R / s⌋₊ + 1) := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      rw [Finset.mem_range]
      exact hbound a ha
    calc (A.card : ℝ) = ((A.image g).card : ℝ) := by rw [hcard]
      _ ≤ ((Finset.range (⌊R / s⌋₊ + 1)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
      _ = ((⌊R / s⌋₊ + 1 : ℕ) : ℝ) := by rw [Finset.card_range]
      _ ≤ R / s + 1 := by
            have := Nat.floor_le (div_nonneg hR hs.le)
            push_cast; linarith

/-- `eNorm` of an integer scalar multiple. -/
lemma eNorm_zsmul (k : ℤ) (v : ι → ℤ) :
    Work.HP.eNorm (k • v) = |(k:ℝ)| * Work.HP.eNorm v :=
  Work.HP.numaux.eNorm_real_smul (c := (k:ℝ)) (fun i => by simp [Pi.smul_apply, smul_eq_mul])

/-- `dotZ` is additive in its first argument. -/
lemma dotZ_sub (x y b : ι → ℤ) :
    Work.HP.dotZ (x - y) b = Work.HP.dotZ x b - Work.HP.dotZ y b := by
  simp only [Work.HP.dotZ_apply, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `dotZ` is additive in its second argument. -/
lemma dotZ_sub_right (x y z : ι → ℤ) :
    Work.HP.dotZ x (y - z) = Work.HP.dotZ x y - Work.HP.dotZ x z := by
  rw [Work.HP.dotZ_comm x (y - z), dotZ_sub, Work.HP.dotZ_comm y x,
    Work.HP.dotZ_comm z x]

/-- `dotZ` is multiplicative in its second argument. -/
lemma dotZ_smul_right (m : ℤ) (x b : ι → ℤ) :
    Work.HP.dotZ x (m • b) = m * Work.HP.dotZ x b := by
  rw [Work.HP.dotZ_comm x (m • b), Work.HP.dotZ_smul, Work.HP.dotZ_comm b x]

/-- The squared norm of the scaled projection, expanded: the cross terms cancel. -/
lemma dotZ_projScale_self (u a : ι → ℤ) :
    Work.HP.dotZ (Work.HP.projScale u a) (Work.HP.projScale u a)
      = (Work.HP.dotZ u u) ^ 2 * Work.HP.dotZ a a
        - (Work.HP.dotZ u u) * (Work.HP.dotZ a u) ^ 2 := by
  rw [Work.HP.projScale_apply, dotZ_sub, dotZ_sub_right, dotZ_sub_right,
    Work.HP.dotZ_smul, Work.HP.dotZ_smul, Work.HP.dotZ_smul, Work.HP.dotZ_smul,
    dotZ_smul_right, dotZ_smul_right, dotZ_smul_right, dotZ_smul_right,
    Work.HP.dotZ_comm u a]
  ring

/-- `projScale u` is `‖u‖²` times the orthogonal projection onto `u^⊥`, hence `‖u‖²`-Lipschitz. -/
lemma eNorm_projScale_le (u a : ι → ℤ) :
    Work.HP.eNorm (Work.HP.projScale u a) ≤ Work.HP.eNorm u ^ 2 * Work.HP.eNorm a := by
  have hsq : Work.HP.eNorm (Work.HP.projScale u a) ^ 2
      = ((Work.HP.dotZ (Work.HP.projScale u a) (Work.HP.projScale u a) : ℤ) : ℝ) :=
    Work.HP.eNorm_sq_eq _
  have hkey : Work.HP.eNorm (Work.HP.projScale u a) ^ 2
      ≤ (Work.HP.eNorm u ^ 2 * Work.HP.eNorm a) ^ 2 := by
    rw [hsq, dotZ_projScale_self]
    have hc : ((Work.HP.dotZ u u : ℤ) : ℝ) = Work.HP.eNorm u ^ 2 :=
      (Work.HP.eNorm_sq_eq u).symm
    have ha : ((Work.HP.dotZ a a : ℤ) : ℝ) = Work.HP.eNorm a ^ 2 :=
      (Work.HP.eNorm_sq_eq a).symm
    push_cast
    rw [hc, ha]
    have hX : (Work.HP.eNorm u ^ 2 * Work.HP.eNorm a) ^ 2
        = (Work.HP.eNorm u ^ 2) ^ 2 * (Work.HP.eNorm a) ^ 2 := by ring
    rw [hX]
    have : 0 ≤ Work.HP.eNorm u ^ 2 * ((Work.HP.dotZ a u : ℤ) : ℝ) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  nlinarith [hkey, Work.HP.eNorm_nonneg (Work.HP.projScale u a),
    mul_nonneg (sq_nonneg (Work.HP.eNorm u)) (Work.HP.eNorm_nonneg a)]

/-- If `v` and `v'` have the same scaled projection onto `u`, then `‖u‖ ‖v - v'‖` equals the
absolute value of the difference of their pairings with `u`. -/
lemma eNorm_mul_eNorm_sub_eq_abs_dotZ (u : ι → ℤ) (hu0 : u ≠ 0) {v v' : ι → ℤ}
    (h : Work.HP.projScale u v = Work.HP.projScale u v') :
    Work.HP.eNorm u * Work.HP.eNorm (v - v')
      = |((Work.HP.dotZ v u : ℤ) : ℝ) - ((Work.HP.dotZ v' u : ℤ) : ℝ)| := by
  have hc : (Work.HP.dotZ u u) • (v - v')
      = (Work.HP.dotZ v u - Work.HP.dotZ v' u) • u := by
    rw [Work.HP.projScale_apply, Work.HP.projScale_apply] at h
    rw [smul_sub, sub_smul]
    linear_combination h
  have hnorm := congrArg Work.HP.eNorm hc
  rw [eNorm_zsmul, eNorm_zsmul] at hnorm
  have hdu : ((Work.HP.dotZ v u - Work.HP.dotZ v' u : ℤ) : ℝ)
      = ((Work.HP.dotZ v u : ℤ) : ℝ) - ((Work.HP.dotZ v' u : ℤ) : ℝ) := by push_cast; ring
  rw [hdu, abs_of_nonneg (by rw [← Work.HP.eNorm_sq_eq u]; positivity)] at hnorm
  rw [← Work.HP.eNorm_sq_eq u] at hnorm
  have he : Work.HP.eNorm u ≠ 0 := ne_of_gt (Work.HP.eNorm_pos_of_ne_zero hu0)
  have key := hnorm
  rw [pow_two, mul_assoc] at key
  rw [mul_comm (|((Work.HP.dotZ v u : ℤ) : ℝ) - ((Work.HP.dotZ v' u : ℤ) : ℝ)|)
    (Work.HP.eNorm u)] at key
  exact mul_left_cancel₀ he key

theorem ballCount_projScale_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (u : ι → ℤ) (hu : u ∈ L) (hu0 : u ≠ 0)
    (hshort : ∀ v ∈ L, v ≠ 0 → Work.HP.eNorm u ≤ Work.HP.eNorm v) (T : ℝ) (hT : 0 ≤ T) :
    (Work.HP.ballCount L T : ℝ) ≤ (2 * T / Work.HP.eNorm u + 1) *
      (Work.HP.ballCount (Submodule.map (Work.HP.projScale u) L)
        (Work.HP.eNorm u ^ 2 * T) : ℝ) := by
  have hu_pos : 0 < Work.HP.eNorm u := Work.HP.eNorm_pos_of_ne_zero hu0
  have hdiv0 : 0 ≤ 2 * T / Work.HP.eNorm u := div_nonneg (by linarith) hu_pos.le
  set S : Set (ι → ℤ) := {v | v ∈ L ∧ Work.HP.eNorm v ≤ T} with hS
  set S' : Set (ι → ℤ) :=
    {w | w ∈ Submodule.map (Work.HP.projScale u) L ∧ Work.HP.eNorm w ≤ Work.HP.eNorm u ^ 2 * T}
    with hS'
  have hSmem : ∀ v : ι → ℤ, v ∈ S ↔ v ∈ L ∧ Work.HP.eNorm v ≤ T := by
    intro v; simp [hS]
  have hS'mem : ∀ w : ι → ℤ, w ∈ S' ↔
      w ∈ Submodule.map (Work.HP.projScale u) L ∧ Work.HP.eNorm w ≤ Work.HP.eNorm u ^ 2 * T := by
    intro w; simp [hS']
  have hSfin : S.Finite := (Work.HP.MDBasic.finite_eNorm_le T).subset (fun v hv => (hSmem v).mp hv |>.2)
  have hS'fin : S'.Finite :=
    (Work.HP.MDBasic.finite_eNorm_le (Work.HP.eNorm u ^ 2 * T)).subset
      (fun w hw => (hS'mem w).mp hw |>.2)
  set s : Finset (ι → ℤ) := hSfin.toFinset with hs
  set t : Finset (ι → ℤ) := hS'fin.toFinset with ht
  have hms : ∀ a, a ∈ s ↔ a ∈ S := fun a => hSfin.mem_toFinset
  have hmt : ∀ b, b ∈ t ↔ b ∈ S' := fun b => hS'fin.mem_toFinset
  have hmaps : ∀ a ∈ s, Work.HP.projScale u a ∈ t := by
    intro a ha
    rw [hmt, hS'mem]
    obtain ⟨haL, haT⟩ := (hSmem a).mp ((hms a).mp ha)
    refine ⟨Submodule.mem_map.mpr ⟨a, haL, rfl⟩, ?_⟩
    exact (eNorm_projScale_le u a).trans (mul_le_mul_of_nonneg_left haT (by positivity))
  have hfiber : ∀ b ∈ t, #{a ∈ s | Work.HP.projScale u a = b} ≤ ⌊2 * T / Work.HP.eNorm u⌋₊ + 1 := by
    intro b hb
    set Fb : Finset (ι → ℤ) := s.filter (fun a => Work.HP.projScale u a = b) with hFb
    show Fb.card ≤ ⌊2 * T / Work.HP.eNorm u⌋₊ + 1
    set ψ : (ι → ℤ) → ℤ := fun a => Work.HP.dotZ a u with hψ
    have hinj : Set.InjOn ψ ↑Fb := by
      intro a ha a' ha' h
      rw [Finset.mem_coe, hFb, Finset.mem_filter] at ha ha'
      obtain ⟨_, ha_f⟩ := ha
      obtain ⟨_, ha'_f⟩ := ha'
      have hdot : Work.HP.dotZ a u = Work.HP.dotZ a' u := h
      have hid := eNorm_mul_eNorm_sub_eq_abs_dotZ u hu0 (v := a) (v' := a')
        (by rw [ha_f, ha'_f])
      rw [hdot, sub_self, abs_zero] at hid
      have hez : Work.HP.eNorm (a - a') = 0 := by
        rcases mul_eq_zero.mp hid with h1 | h1
        · exact absurd h1 (ne_of_gt hu_pos)
        · exact h1
      exact sub_eq_zero.mp (by
        by_contra hne
        exact absurd hez (ne_of_gt (Work.HP.eNorm_pos_iff.mpr hne)))
    have hcard : (Fb.image ψ).card = Fb.card := Finset.card_image_of_injOn hinj
    have hsep : ∀ a ∈ Fb.image ψ, ∀ a' ∈ Fb.image ψ, a ≠ a' →
        Work.HP.eNorm u ^ 2 ≤ |(a:ℝ) - (a':ℝ)| := by
      intro a ha a' ha' hne
      rw [Finset.mem_image] at ha ha'
      obtain ⟨v, hv, rfl⟩ := ha
      obtain ⟨v', hv', rfl⟩ := ha'
      rw [hFb, Finset.mem_filter] at hv hv'
      obtain ⟨hv_s, hv_f⟩ := hv
      obtain ⟨hv'_s, hv'_f⟩ := hv'
      obtain ⟨hvL, _⟩ := (hSmem v).mp ((hms v).mp hv_s)
      obtain ⟨hv'L, _⟩ := (hSmem v').mp ((hms v').mp hv'_s)
      have hvv' : v ≠ v' := fun h => hne (by rw [h])
      have hid := eNorm_mul_eNorm_sub_eq_abs_dotZ u hu0 (v := v) (v' := v')
        (by rw [hv_f, hv'_f])
      change Work.HP.eNorm u ^ 2
        ≤ |((Work.HP.dotZ v u : ℤ) : ℝ) - ((Work.HP.dotZ v' u : ℤ) : ℝ)|
      rw [← hid]
      have hge : Work.HP.eNorm u ≤ Work.HP.eNorm (v - v') :=
        hshort (v - v') (Submodule.sub_mem L hvL hv'L) (sub_ne_zero.mpr hvv')
      calc Work.HP.eNorm u ^ 2 = Work.HP.eNorm u * Work.HP.eNorm u := by ring
        _ ≤ Work.HP.eNorm u * Work.HP.eNorm (v - v') :=
            mul_le_mul_of_nonneg_left hge (Work.HP.eNorm_nonneg u)
    have hbd : ∀ a ∈ Fb.image ψ, ∀ a' ∈ Fb.image ψ,
        |(a:ℝ) - (a':ℝ)| ≤ 2 * T * Work.HP.eNorm u := by
      intro a ha a' ha'
      rw [Finset.mem_image] at ha ha'
      obtain ⟨v, hv, rfl⟩ := ha
      obtain ⟨v', hv', rfl⟩ := ha'
      rw [hFb, Finset.mem_filter] at hv hv'
      obtain ⟨hv_s, hv_f⟩ := hv
      obtain ⟨hv'_s, hv'_f⟩ := hv'
      obtain ⟨_, hvT⟩ := (hSmem v).mp ((hms v).mp hv_s)
      obtain ⟨_, hv'T⟩ := (hSmem v').mp ((hms v').mp hv'_s)
      have hid := eNorm_mul_eNorm_sub_eq_abs_dotZ u hu0 (v := v) (v' := v')
        (by rw [hv_f, hv'_f])
      change |((Work.HP.dotZ v u : ℤ) : ℝ) - ((Work.HP.dotZ v' u : ℤ) : ℝ)|
        ≤ 2 * T * Work.HP.eNorm u
      rw [← hid]
      calc Work.HP.eNorm u * Work.HP.eNorm (v - v')
          ≤ Work.HP.eNorm u * (Work.HP.eNorm v + Work.HP.eNorm v') :=
            mul_le_mul_of_nonneg_left (eNorm_sub_le v v') (Work.HP.eNorm_nonneg u)
        _ ≤ Work.HP.eNorm u * (T + T) := by
            apply mul_le_mul_of_nonneg_left _ (Work.HP.eNorm_nonneg u); linarith
        _ = 2 * T * Work.HP.eNorm u := by ring
    have hkey := card_le_of_separated (A := Fb.image ψ) (s := Work.HP.eNorm u ^ 2)
        (R := 2 * T * Work.HP.eNorm u) (pow_pos hu_pos 2) (by positivity) hsep hbd
    have hsimp : (2 * T * Work.HP.eNorm u) / Work.HP.eNorm u ^ 2
        = 2 * T / Work.HP.eNorm u := by
      field_simp
    rw [hsimp] at hkey
    rw [← hcard]
    have hfl := Nat.le_floor hkey
    rwa [Nat.floor_add_one hdiv0] at hfl
  have hmain : s.card ≤ (⌊2 * T / Work.HP.eNorm u⌋₊ + 1) * t.card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps _ hfiber
  have hscard : s.card = Work.HP.ballCount L T := by
    rw [← Set.ncard_coe_finset s, hSfin.coe_toFinset]
    rfl
  have htcard : t.card
      = Work.HP.ballCount (Submodule.map (Work.HP.projScale u) L) (Work.HP.eNorm u ^ 2 * T) := by
    rw [← Set.ncard_coe_finset t, hS'fin.coe_toFinset]
    rfl
  have hfin : (s.card : ℝ) ≤ (2 * T / Work.HP.eNorm u + 1) * (t.card : ℝ) := by
    have h1 : ((⌊2 * T / Work.HP.eNorm u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T / Work.HP.eNorm u + 1 := by
      have := Nat.floor_le hdiv0
      push_cast; linarith
    have h2 : (s.card : ℝ) ≤ ((⌊2 * T / Work.HP.eNorm u⌋₊ + 1 : ℕ) : ℝ) * (t.card : ℝ) := by
      exact_mod_cast hmain
    exact h2.trans (mul_le_mul_of_nonneg_right h1 (by positivity))
  rw [hscard, htcard] at hfin
  exact hfin

end Work.HP.MDEstimates
