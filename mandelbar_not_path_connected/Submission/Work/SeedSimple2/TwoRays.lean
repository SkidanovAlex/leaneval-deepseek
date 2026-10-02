/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2 — item `TR`: the mod-1 two-ray portrait from `RN0`, `GF`, the certificate `C` and `U`

`NOTES_LEAD_mandelbar_seed.md` §4.2, item `TR`.  The two geometric inputs enter as explicit
hypotheses:

* `hRN0` — rotation number zero: every angle landing at `z₁` is fixed by the angle map
  `θ ↦ 1024 θ mod 1` (item `RN0`, proved from the tail order `O`, the correspondence `M` and the
  shift `L` in the sibling files of this area);
* `hGF` — the `g`-fixed rays avoid the wake arc `(α₁, α₂)` (item `GF`).

Everything else is here: the finite certificate `C` (`Cert.lean`), the unlinked lemma `U`
(`Unlinked/unlinked_of_coLands.lean`) and the exact-period-5 bookkeeping of `EL.RootParabolic`.
-/
import Submission.Work.SeedSimple2.Cert
import Submission.Work.SeedSimple2.Invariance
import Submission.Work.FSeed.Rays.landsAt_periodic
import Submission.Work.ELTop.landsN_iff_landsAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Function
open scoped Topology

noncomputable section

namespace Work.SeedSimple2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ}

/-! ## Bridges between the landing vocabularies -/

theorem landsN_iff_landsAt (d : Work.EL.RootParabolic c) {θ : ℝ} {z : ℂ} :
    Work.EL.LandsN d.hN θ z ↔ Work.Landing.landsAt c θ z :=
  Work.ELTop.landsN_iff_landsAt d.hN d.bottcher θ z

/-- `landsAt` only depends on the angle modulo `1`. -/
theorem landsN_add_int (d : Work.EL.RootParabolic c) {θ : ℝ} {z : ℂ} (n : ℤ) :
    Work.EL.LandsN d.hN (θ + n) z ↔ Work.EL.LandsN d.hN θ z := by
  rw [landsN_iff_landsAt d, landsN_iff_landsAt d, Work.FSeed.landsAt_add_int_iff n]

theorem EL_T_iterate_add (a b : ℕ) (x : ℝ) :
    (Work.EL.T^[a]) ((Work.EL.T^[b]) x) = (Work.EL.T^[a + b]) x := by
  rw [Function.iterate_add_apply]

theorem Tantibar_iterate_add (a b : ℕ) (x : ℂ) :
    (Tantibar c)^[a] ((Tantibar c)^[b] x) = (Tantibar c)^[a + b] x := by
  rw [Function.iterate_add_apply]

theorem alpha1_div : ((371 : ℝ) / 1023) = Work.EL.alpha1 := by
  norm_num [Work.EL.alpha1]

theorem alpha2_div : ((404 : ℝ) / 1023) = Work.EL.alpha2 := by
  norm_num [Work.EL.alpha2]

/-- Every landing ray gives an element of the angle set `A`. -/
theorem fract_mem_LandAngles (d : Work.EL.RootParabolic c) {θ : ℝ}
    (h : Work.Landing.landsAt c θ d.z₁) : Int.fract θ ∈ LandAngles d.hN d.z₁ :=
  ⟨⟨Int.fract_nonneg θ, Int.fract_lt_one θ⟩,
    (landsN_iff_landsAt d).mpr (Work.FSeed.landsAt_fract_iff.mpr h)⟩

/-! ## `RN0` in the denominator-`1023` form -/

theorem eq_div_of_fract_1024 {θ : ℝ} (hθ : θ ∈ Set.Ico 0 1)
    (h : Int.fract (1024 * θ) = θ) : ∃ j : ℕ, j < 1023 ∧ θ = (j : ℝ) / 1023 := by
  obtain ⟨h0, h1⟩ := hθ
  obtain ⟨-, -, z, hz⟩ := (Int.fract_eq_iff (a := 1024 * θ) (b := θ)).mp h
  have hz' : (1023 : ℝ) * θ = (z : ℝ) := by linarith
  have hz0 : 0 ≤ z := by
    have : (0 : ℝ) ≤ (z : ℝ) := by rw [← hz']; positivity
    exact_mod_cast this
  have hzlt : z < 1023 := by
    have : (z : ℝ) < 1023 := by rw [← hz']; nlinarith
    exact_mod_cast this
  refine ⟨z.toNat, ?_, ?_⟩
  · have : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    omega
  · have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hz0]
    rw [hcast, ← hz']
    field_simp

/-! ## The period-`5` bookkeeping -/

theorem iterate_ne_of_lt (d : Work.EL.RootParabolic c) {i k : ℕ} (hi : i ≤ 5) (hik : i < k)
    (hk : k < 5) : (Tantibar c)^[i] d.z₁ ≠ (Tantibar c)^[k] d.z₁ := by
  intro h
  have hm : 0 < k - i := Nat.sub_pos_of_lt hik
  have hm5 : k - i < 5 := by omega
  have hper : (Tantibar c)^[k - i] ((Tantibar c)^[i] d.z₁) = (Tantibar c)^[i] d.z₁ := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hik)]
    exact h.symm
  have hz1 : d.z₁ = (Tantibar c)^[5 - i] ((Tantibar c)^[i] d.z₁) := by
    nth_rewrite 1 [← d.per_half]
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi]
  have hadd : ∀ (a b : ℕ) (x : ℂ),
      (Tantibar c)^[a] ((Tantibar c)^[b] x) = (Tantibar c)^[a + b] x := by
    intro a b x
    rw [Function.iterate_add_apply]
  have hfin : (Tantibar c)^[k - i] d.z₁ = d.z₁ := by
    conv_lhs => rw [hz1]
    rw [hadd (k - i) (5 - i) ((Tantibar c)^[i] d.z₁),
      show (k - i) + (5 - i) = (5 - i) + (k - i) from Nat.add_comm _ _,
      ← hadd (5 - i) (k - i) ((Tantibar c)^[i] d.z₁), hper, ← hz1]
  exact d.ne_per (k - i) (Finset.mem_Ioo.mpr ⟨hm, hm5⟩) hfin

/-! ## The angles of the certificate are landing rays -/

theorem TN_iterate_lt (j i : ℕ) (hj : j < 1023) : (TN^[i]) j < 1023 := by
  induction i with
  | zero => simpa using hj
  | succ i ih => rw [Function.iterate_succ_apply']; exact TN_lt _

theorem fract_div_1023 (a : ℕ) (ha : a < 1023) :
    Int.fract (((a : ℕ) : ℝ) / 1023) = ((a : ℕ) : ℝ) / 1023 :=
  Int.fract_eq_self.mpr ⟨by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast ha⟩

/-- **The angles of `levelSet j i` are landing rays at `(T_c)^[i] z₁`**, with representatives
`< 1023`. -/
theorem landsN_levelSet (d : Work.EL.RootParabolic c) {j : ℕ} (hj : j < 1023)
    (hθ₀ : Work.EL.LandsN d.hN ((j : ℝ) / 1023) d.z₁) {i a : ℕ}
    (ha : a ∈ levelSet j i) :
    a < 1023 ∧ Work.EL.LandsN d.hN ((a : ℝ) / 1023) ((Tantibar c)^[i] d.z₁) := by
  have ha' : a ∈ levelAngles j i := List.mem_eraseDups.mp ha
  simp only [levelAngles, α₁N, α₂N, List.mem_cons, List.mem_nil_iff, or_false] at ha'
  have hα₁ : Work.EL.LandsN d.hN ((371 : ℝ) / 1023) d.z₁ := by
    rw [show ((371 : ℝ) / 1023) = Work.EL.alpha1 by norm_num [Work.EL.alpha1]]
    exact (landsN_iff_landsAt d).mpr d.rays.1
  have hα₂ : Work.EL.LandsN d.hN ((404 : ℝ) / 1023) d.z₁ := by
    rw [show ((404 : ℝ) / 1023) = Work.EL.alpha2 by norm_num [Work.EL.alpha2]]
    exact (landsN_iff_landsAt d).mpr d.rays.2
  rcases ha' with h | h | h | h
  · subst h
    refine ⟨TN_iterate_lt 371 i (by norm_num), ?_⟩
    rw [← T_iterate_div]
    exact landsN_T_iterate d i hα₁
  · subst h
    refine ⟨TN_iterate_lt 404 i (by norm_num), ?_⟩
    rw [← T_iterate_div]
    exact landsN_T_iterate d i hα₂
  · subst h
    refine ⟨TN_iterate_lt j i hj, ?_⟩
    rw [← T_iterate_div]
    exact landsN_T_iterate d i hθ₀
  · subst h
    have hg : ((gN j : ℕ) : ℝ) / 1023 = (Work.EL.T^[5]) ((j : ℝ) / 1023) := by
      show (((TN^[5]) j : ℕ) : ℝ) / 1023 = (Work.EL.T^[5]) ((j : ℝ) / 1023)
      rw [T_iterate_div]
    refine ⟨TN_iterate_lt (gN j) i (TN_iterate_lt j 5 hj), ?_⟩
    rw [← T_iterate_div, hg]
    have h := landsN_T_iterate d (i + 5) hθ₀
    rw [← EL_T_iterate_add i 5, ← Tantibar_iterate_add (c := c) i 5, d.per_half] at h
    exact h

/-! ## The contradiction produced by a linked pair -/

theorem linking_step (d : Work.EL.RootParabolic c) (hJ : Work.Top.JordanForm)
    (hU : ∀ {a b a' b' : ℝ} {w w' : ℂ}, w ≠ w' →
      a ∈ Set.Ico 0 1 → b ∈ Set.Ico 0 1 → a' ∈ Set.Ico 0 1 → b' ∈ Set.Ico 0 1 →
      Work.EL.LandsN d.hN a w → Work.EL.LandsN d.hN b w → Work.EL.LandsN d.hN a' w' →
      Work.EL.LandsN d.hN b' w' → PairwiseDistinct4 a b a' b' →
      Work.ELPull.Unlinked a b a' b')
    {j : ℕ} (hj : j < 1023) (hθ₀ : Work.EL.LandsN d.hN ((j : ℝ) / 1023) d.z₁)
    {i k a b e f : ℕ} (hi : i < 5) (hk : k < 5) (hik : i < k)
    (ha : a ∈ levelSet j i) (hb : b ∈ levelSet j i) (hab : a ≠ b)
    (he : e ∈ levelSet j k) (hf : f ∈ levelSet j k) (hef : e ≠ f)
    (hlink : unlinkedB a b e f = false) : False := by
  obtain ⟨hlt_a, hla⟩ := landsN_levelSet d hj hθ₀ ha
  obtain ⟨hlt_b, hlb⟩ := landsN_levelSet d hj hθ₀ hb
  obtain ⟨hlt_e, hle⟩ := landsN_levelSet d hj hθ₀ he
  obtain ⟨hlt_f, hlf⟩ := landsN_levelSet d hj hθ₀ hf
  have hper := iterate_ne_of_lt d (i := i) (k := k) (by omega) hik (by omega)
  have hnu := not_unlinked_of_unlinkedB_false a b e f hlt_a hlt_b hlt_e hlt_f hlink
  by_cases hcoin : a = e ∨ a = f ∨ b = e ∨ b = f
  · have key : ∀ {x y s t : ℕ}, x ∈ levelSet j s → y ∈ levelSet j t → x = y →
        (Tantibar c)^[s] d.z₁ = (Tantibar c)^[t] d.z₁ := by
      intro x y s t hx hy hxy
      obtain ⟨-, hlx⟩ := landsN_levelSet d hj hθ₀ hx
      obtain ⟨-, hly⟩ := landsN_levelSet d hj hθ₀ hy
      rw [hxy] at hlx
      exact landsN_unique hlx hly
    rcases hcoin with h | h | h | h
    · exact hper (key ha he h)
    · exact hper (key ha hf h)
    · exact hper (key hb he h)
    · exact hper (key hb hf h)
  · have hre : ∀ x y : ℕ, x < 1023 → y < 1023 → x ≠ y →
        ((x : ℝ) / 1023 : ℝ) ≠ (y : ℝ) / 1023 := by
      intro x y hx hy hxy h
      have h' : (x : ℝ) = (y : ℝ) := by
        have hh := h
        field_simp at hh
        linarith
      exact hxy (by exact_mod_cast h')
    have hd : PairwiseDistinct4 ((a : ℝ) / 1023) ((b : ℝ) / 1023) ((e : ℝ) / 1023)
        ((f : ℝ) / 1023) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [fract_div_1023 a hlt_a, fract_div_1023 b hlt_b]; exact hre a b hlt_a hlt_b hab
      · rw [fract_div_1023 a hlt_a, fract_div_1023 e hlt_e]
        exact hre a e hlt_a hlt_e (fun hh => hcoin (Or.inl hh))
      · rw [fract_div_1023 a hlt_a, fract_div_1023 f hlt_f]
        exact hre a f hlt_a hlt_f (fun hh => hcoin (Or.inr (Or.inl hh)))
      · rw [fract_div_1023 b hlt_b, fract_div_1023 e hlt_e]
        exact hre b e hlt_b hlt_e (fun hh => hcoin (Or.inr (Or.inr (Or.inl hh))))
      · rw [fract_div_1023 b hlt_b, fract_div_1023 f hlt_f]
        exact hre b f hlt_b hlt_f (fun hh => hcoin (Or.inr (Or.inr (Or.inr hh))))
      · rw [fract_div_1023 e hlt_e, fract_div_1023 f hlt_f]; exact hre e f hlt_e hlt_f hef
    have hsub : Work.ELPull.Unlinked ((a : ℝ) / 1023) ((b : ℝ) / 1023) ((e : ℝ) / 1023)
        ((f : ℝ) / 1023) :=
      hU hper
        ⟨by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast hlt_a⟩
        ⟨by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast hlt_b⟩
        ⟨by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast hlt_e⟩
        ⟨by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast hlt_f⟩
        hla hlb hle hlf hd
    exact hnu hsub

/-! ## The mod-`1` portrait -/

theorem twoRays_of_inputs (d : Work.EL.RootParabolic c) (hJ : Work.Top.JordanForm)
    (hU : ∀ {a b a' b' : ℝ} {w w' : ℂ}, w ≠ w' →
      a ∈ Set.Ico 0 1 → b ∈ Set.Ico 0 1 → a' ∈ Set.Ico 0 1 → b' ∈ Set.Ico 0 1 →
      Work.EL.LandsN d.hN a w → Work.EL.LandsN d.hN b w → Work.EL.LandsN d.hN a' w' →
      Work.EL.LandsN d.hN b' w' → PairwiseDistinct4 a b a' b' →
      Work.ELPull.Unlinked a b a' b')
    (hRN0 : ∀ θ ∈ LandAngles d.hN d.z₁, Int.fract (1024 * θ) = θ)
    (hGF : ∀ θ ∈ LandAngles d.hN d.z₁, IsGFixed θ →
      ¬ Work.ELPull.InArc θ Work.EL.alpha1 Work.EL.alpha2) :
    Work.FSeed.LocalRayPortrait c d.z₁ := by
  have hmem : ∀ θ : ℝ, Work.Landing.landsAt c θ d.z₁ → Int.fract θ ∈ LandAngles d.hN d.z₁ :=
    fun θ h => fract_mem_LandAngles d h
  have key : ∀ x : ℝ, x ∈ LandAngles d.hN d.z₁ → x = Work.EL.alpha1 ∨ x = Work.EL.alpha2 := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := eq_div_of_fract_1024 hx.1 (hRN0 x hx)
    have hθ₀ : Work.EL.LandsN d.hN ((j : ℝ) / 1023) d.z₁ := by
      rw [← hxj]
      exact hx.2
    have keyj : ((j : ℝ) / 1023 : ℝ) = Work.EL.alpha1 ∨ ((j : ℝ) / 1023 : ℝ) = Work.EL.alpha2 := by
      by_cases hjs : j ∈ survivors
      · simp only [survivors, Finset.mem_insert, Finset.mem_singleton] at hjs
        rcases hjs with h | h | h | h
        · subst h; exact Or.inl alpha1_div
        · subst h
          exfalso
          rw [hxj] at hx
          have hfix : IsGFixed ((372 : ℝ) / 1023) := by
            show Work.EL.T (Work.EL.T (Work.EL.T (Work.EL.T (Work.EL.T ((372 : ℝ) / 1023))))) =
              (372 : ℝ) / 1023
            norm_num [Work.EL.T, Int.fract]
          exact hGF _ hx hfix inArc_372
        · subst h
          exfalso
          rw [hxj] at hx
          have hfix : IsGFixed ((403 : ℝ) / 1023) := by
            show Work.EL.T (Work.EL.T (Work.EL.T (Work.EL.T (Work.EL.T ((403 : ℝ) / 1023))))) =
              (403 : ℝ) / 1023
            norm_num [Work.EL.T, Int.fract]
          exact hGF _ hx hfix inArc_403
        · subst h; exact Or.inr alpha2_div
      · exfalso
        have hcert := certB_of_not_survivor j hj hjs
        obtain ⟨i, k, hi, hk, hik, hlink⟩ := certB_imp j hcert
        obtain ⟨a, ha, b, hb, hab, e, he, f, hf, hef, huf⟩ :=
          linkedLevels_of_linkedLevelsB hlink
        exact linking_step d hJ hU hj hθ₀ hi hk hik ha hb hab he hf hef huf
    rw [hxj]
    exact keyj
  refine ⟨fun θ θ' θ'' hθ hθ' hθ'' => ?_⟩
  rcases key _ (hmem θ hθ) with h1 | h1 <;> rcases key _ (hmem θ' hθ') with h2 | h2 <;>
    rcases key _ (hmem θ'' hθ'') with h3 | h3 <;>
    simp only [h1, h2, h3] <;> tauto

end Work.SeedSimple2

end
