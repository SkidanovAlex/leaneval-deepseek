/-
Assembly for the family packing of famQuad t: χ₂ is well-defined per circle
(fam_pairChi_wd), constant −1 on every coprime tangent pair over the whole
circle graph (anchored at fam_anchor on the root pair (famA t, famB t)), and
consequently no square curvature occurs in the packing of famQuad t.

(Family analogue of Assembly.lean.)
-/
import Submission.Apollo.FamWD
import Submission.Apollo.FamOccurrence
import Submission.Apollo.FamCrack
import Submission.Apollo.ChiCross
import Submission.Apollo.KR
import Submission.Apollo.Base
import Submission.Apollo.Structure
import Submission.Apollo.Assembly
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-! ## coprime tangent partner existence (crack detour, family) -/

/-- a coprime tangent partner of the circle at (w,i) exists (family). -/
theorem copartner_exists_fam (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) : ∃ c : ℤ, RingCopartner w i c := by
  let σ : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) i
  have hσ0 : σ 0 = i := by
    dsimp [σ]
    simp
  rcases crack_pair_coprime_exists_at_fam t w hw σ with
    ⟨u, huorb, hun, hfix0, hfix1, z, hz, k, hk, huk⟩
  refine ⟨z, ?_⟩
  have hz0 : z.gcd (w i) = 1 := by
    have hzσ : z.gcd (w (σ 0)) = 1 := gcd_of_gcd_mul_left hz
    rwa [hσ0] at hzσ
  have hkne : k ≠ i := by
    intro hk_i
    have hk0 : k = σ 0 := by rwa [← hσ0] at hk_i
    rcases hk with hk2 | hk3
    · have : σ 2 = σ 0 := hk2.symm.trans hk0
      exact (by decide : (2 : Fin 4) ≠ 0) ((Equiv.injective σ) this)
    · have : σ 3 = σ 0 := hk3.symm.trans hk0
      exact (by decide : (3 : Fin 4) ≠ 0) ((Equiv.injective σ) this)
  refine ⟨u, ?_, k, hkne, huk, hz0⟩
  rw [← hσ0]
  rcases hun with ⟨n, rfl⟩
  exact ringReach_relabelCrack σ w n

/-- chosen coprime tangent partner of the circle at (w,i) (family). -/
noncomputable def ringPartner_fam (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) : ℤ :=
  Classical.choose (copartner_exists_fam t w hw i)

/-- the intrinsic χ₂ of the circle at (w,i) in the family packing. -/
noncomputable def circleChi_fam (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) : ℤ :=
  pairChi (w i) (ringPartner_fam t w hw i)

/-- the chosen partner really is a coprime tangent partner (family). -/
lemma ringPartner_spec_fam (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) : RingCopartner w i (ringPartner_fam t w hw i) :=
  Classical.choose_spec (copartner_exists_fam t w hw i)

/-- circleChi_fam equals the symbol against ANY coprime tangent partner. -/
theorem circleChi_eq_partner_fam (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) {c : ℤ} (hc : RingCopartner w i c) :
    circleChi_fam t w hw i = pairChi (w i) c := by
  unfold circleChi_fam
  exact (fam_pairChi_wd t w hw i c (ringPartner_fam t w hw i) hc (ringPartner_spec_fam t w hw i)).symm

/-- circleChi_fam does not depend on the orbit-membership proof. -/
lemma circleChi_irrel_fam (t : ℕ) (w : Fin 4 → ℤ) (i : Fin 4) {hw hw' : w ∈ orbitOf (famQuad t)} :
    circleChi_fam t w hw i = circleChi_fam t w hw' i := by
  unfold circleChi_fam ringPartner_fam
  exact congrArg (fun h : ∃ c : ℤ, RingCopartner w i c => pairChi (w i) (Classical.choose h))
    (Subsingleton.elim (copartner_exists_fam t w hw i) (copartner_exists_fam t w hw' i))

/-- circleChi_fam is invariant along ring walks: it depends only on the circle. -/
theorem circleChi_ringReach_fam (t : ℕ) {w u : Fin 4 → ℤ} (hw : w ∈ orbitOf (famQuad t))
    (hu : u ∈ orbitOf (famQuad t)) (i : Fin 4) (hring : ringReach i w u) :
    circleChi_fam t w hw i = circleChi_fam t u hu i := by
  calc
    circleChi_fam t w hw i = pairChi (w i) (ringPartner_fam t u hu i) :=
      circleChi_eq_partner_fam t w hw i
        (ringCopartner_of_ringReach i (ringReach_symm hring) (ringPartner_fam t u hu i)
          (ringPartner_spec_fam t u hu i))
    _ = pairChi (u i) (ringPartner_fam t u hu i) := by
      have hui : u i = w i := (formValues_of_ringReach w i u hring).1
      unfold pairChi
      rw [← hui]
    _ = circleChi_fam t u hu i := by
      rfl

/-! ## reciprocity on coprime tangent pairs (family) -/

/-- coprime integers cannot both be even. -/
lemma not_coprime_of_both_even_fam {x y : ℤ} (hx : 2 ∣ x) (hy : 2 ∣ y) : x.gcd y ≠ 1 := by
  rw [Int.gcd_eq_natAbs]
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simp only [Int.natAbs_mul]
  norm_num
  have hg : Nat.gcd (2 * a.natAbs) (2 * b.natAbs) = 2 * Nat.gcd a.natAbs b.natAbs := by
    rw [Nat.gcd_mul_left]
  rw [hg]
  omega

/-- χ₂ is symmetric on coprime co-occurring pairs (reciprocity, family). -/
theorem pairChi_symm_tangent_fam (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i j : Fin 4) (hij : i ≠ j) (hcop : (w j).gcd (w i) = 1) :
    pairChi (w i) (w j) = pairChi (w j) (w i) := by
  have hpos : 0 < w i ∨ 0 < w j := famOrbit_pos_of_two_coords t w hw i j hij
  by_cases hie : 2 ∣ w i
  · by_cases hje : 2 ∣ w j
    · exfalso
      have hg : (w i).gcd (w j) = 1 := by rwa [Int.gcd_comm] at hcop
      exact not_coprime_of_both_even_fam hie hje hg
    · have hjo5 : (w j) % 8 = 5 := famOrbit_odd_val_eight_five t w hw j hje
      exact (pairChi_mixed (o := w j) (e := w i) hjo5 hcop hpos.symm).symm
  · by_cases hje : 2 ∣ w j
    · have hio5 : (w i) % 8 = 5 := famOrbit_odd_val_eight_five t w hw i hie
      have hcop' : (w i).gcd (w j) = 1 := by rwa [Int.gcd_comm] at hcop
      exact pairChi_mixed (o := w i) (e := w j) hio5 hcop' hpos
    · have h4i : (w i) % 4 = 1 := famOrbit_odd_val_four_one t w hw i hie
      have h4j : (w j) % 4 = 1 := famOrbit_odd_val_four_one t w hw j hje
      exact pairChi_odd_odd_symm h4i h4j hpos

/-! ## Prop1step and the occurrence-level χ₂ (family) -/

/-- coprime tangent circles in one family-orbit quadruple have equal χ₂. -/
theorem circleChi_eq_of_coprime_tangent_fam (t : ℕ) (w : Fin 4 → ℤ)
    (hw : w ∈ orbitOf (famQuad t)) (i j : Fin 4) (hij : i ≠ j)
    (hcop : (w j).gcd (w i) = 1) :
    circleChi_fam t w hw i = circleChi_fam t w hw j := by
  calc
    circleChi_fam t w hw i = pairChi (w i) (w j) := by
      exact circleChi_eq_partner_fam t w hw i ⟨w, Relation.ReflTransGen.refl, j, hij.symm, rfl, hcop⟩
    _ = pairChi (w j) (w i) := pairChi_symm_tangent_fam t w hw i j hij hcop
    _ = circleChi_fam t w hw j := by
      exact (circleChi_eq_partner_fam t w hw j ⟨w, Relation.ReflTransGen.refl, i, hij, rfl,
        (by rwa [Int.gcd_comm] at hcop)⟩).symm

/-- circleChi_fam depends only on the quadruple and index, not on the orbit
proof. -/
lemma circleChi_congr_fam (t : ℕ) {w w' : Fin 4 → ℤ} (hww' : w = w')
    {hw : w ∈ orbitOf (famQuad t)} {hw' : w' ∈ orbitOf (famQuad t)} (i : Fin 4) :
    circleChi_fam t w hw i = circleChi_fam t w' hw' i := by
  cases hww'
  exact circleChi_irrel_fam t w i

/-- χ₂ at an occurrence (family). -/
noncomputable def occChi_fam (t : ℕ) (o : Occ) : ℤ := by
  classical
  exact if ho : famValid t o then circleChi_fam t o.1 ho o.2 else 0

/-- χ₂ is invariant under a copath step between family-valid occurrences. -/
theorem occChi_step_fam (t : ℕ) {a b : Occ} (hstep : copathStep a b) (ha : famValid t a)
    (hb : famValid t b) : occChi_fam t a = occChi_fam t b := by
  cases a with | mk w i =>
  cases b with | mk u j =>
  unfold occChi_fam
  rw [dif_pos ha, dif_pos hb]
  rcases hstep with htan | hsame
  · rcases htan with ⟨htan, hcop⟩
    rcases htan with ⟨hw, hne⟩
    change w = u at hw
    have hcopC : coprimeValues (w, i) (u, j) := hcop
    have hcopW : (w j).gcd (w i) = 1 := by
      dsimp [coprimeValues, ovalue] at hcopC
      rw [← hw] at hcopC
      rwa [Int.gcd_comm] at hcopC
    have hmain := circleChi_eq_of_coprime_tangent_fam t w ha i j hne hcopW
    calc
      circleChi_fam t w ha i = circleChi_fam t w ha j := hmain
      _ = circleChi_fam t u hb j := by
        exact circleChi_congr_fam t hw j
  · have hind : i = j := by
      have h' : (w, i).2 = (u, j).2 :=
        eqvGen_preserves (α := Fin 4) (f := fun o : Occ => o.2)
          (fun o₁ o₂ h => replaceStep_index h) hsame
      simpa using h'
    have hsr : ringReach i w u := by
      have hsame' : sameCircle (w, i) (u, i) := by
        rwa [← hind] at hsame
      exact ringReach_of_sameCircle w u i hsame'
    calc
      circleChi_fam t w ha i = circleChi_fam t u hb i := circleChi_ringReach_fam t ha hb i hsr
      _ = circleChi_fam t u hb j := by rw [hind]

/-- family validity is preserved by copath steps. -/
lemma fam_valid_step_of_copathStep (t : ℕ) {a b : Occ} (hstep : copathStep a b)
    (ha : famValid t a) : famValid t b := by
  rcases hstep with htan | hsame
  · rcases htan with ⟨htan, hcop⟩
    rcases htan with ⟨hw, _⟩
    simpa [famValid, hw] using ha
  · exact (fam_sameCircle_valid t hsame).1 ha

/-- χ₂ is constant over the connected circle graph of the family packing. -/
theorem occChi_const_fam (t : ℕ) (o p : Occ) (ho : famValid t o) (hp : famValid t p) :
    occChi_fam t o = occChi_fam t p := by
  have hc : copath o p := fam_occ_copath_valid t o p ho hp
  have hvp : ∀ b : Occ, copath o b → famValid t b := by
    intro b hb
    induction hb with
    | refl => exact ho
    | tail hprev hstep ih => exact fam_valid_step_of_copathStep t hstep ih
  have hval : ∀ b : Occ, copath o b → occChi_fam t o = occChi_fam t b := by
    intro b hb
    induction hb with
    | refl => rfl
    | tail hprev hstep ih =>
        exact ih.trans (occChi_step_fam t hstep (hvp _ hprev)
          (fam_valid_step_of_copathStep t hstep (hvp _ hprev)))
  exact hval p hc

/-- the anchor: at the root quadruple of the family packing the χ₂ value
is −1. -/
lemma occChi_base_fam (t : ℕ) : occChi_fam t (famQuad t, 0) = -1 := by
  unfold occChi_fam
  rw [dif_pos (famValid_of_quad t (famQuad_mem_own_orbit t) 0)]
  calc
    circleChi_fam t (famQuad t) (famQuad_mem_own_orbit t) 0 = pairChi (famQuad t 0) (famQuad t 1) := by
      exact circleChi_eq_partner_fam t (famQuad t) (famQuad_mem_own_orbit t) 0
        ⟨famQuad t, Relation.ReflTransGen.refl, (1 : Fin 4), (by decide : (1 : Fin 4) ≠ 0), rfl,
          (by rw [Int.gcd_comm]; exact famAB_gcd_one t)⟩
    _ = -1 := by
      rw [famQuad_zero]
      simp [famQuad]
      exact fam_anchor t

/-- every coprime tangent partner of any circle of the family packing has
χ₂ = −1. -/
theorem circle_pair_minus_one_fam (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) (c : ℤ) (hc : RingCopartner w i c) : pairChi (w i) c = -1 := by
  have hc2 : circleChi_fam t w hw i = -1 := by
    calc
      circleChi_fam t w hw i = occChi_fam t (w, i) := by
        unfold occChi_fam
        rw [dif_pos (show famValid t (w, i) from hw)]
      _ = occChi_fam t (famQuad t, 0) := occChi_const_fam t (w, i) (famQuad t, 0) hw
        (famValid_of_quad t (famQuad_mem_own_orbit t) 0)
      _ = -1 := occChi_base_fam t
  have hc1 : circleChi_fam t w hw i = pairChi (w i) c := circleChi_eq_partner_fam t w hw i hc
  exact hc1.symm.trans hc2

/-! ## square exclusion for the family packing -/

/-- coprimality to the square implies coprimality to the base (generic). -/
lemma gcd_of_gcd_square_fam {z n : ℤ} (h : z.gcd (n ^ 2) = 1) : z.gcd n = 1 := by
  rw [Int.gcd_eq_natAbs] at h ⊢
  rw [Int.natAbs_pow] at h
  have hd : Nat.gcd z.natAbs n.natAbs ∣ Nat.gcd z.natAbs (n.natAbs ^ 2) := by
    apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left z.natAbs n.natAbs
    · refine dvd_trans (Nat.gcd_dvd_right z.natAbs n.natAbs) ?_
      rw [pow_two]
      exact dvd_mul_right n.natAbs n.natAbs
  rw [h] at hd
  exact Nat.dvd_one.mp hd

/-- no square curvature occurs in the packing of the family quadruple. -/
theorem no_square_fam_orbit (t : ℕ) : ∀ n : ℤ, n ^ 2 ∉
    {x : ℤ | ∃ v ∈ orbitOf (famQuad t), x ∈ Set.range v} := by
  intro n hn
  rcases hn with ⟨w, hw, ⟨i, hwi⟩⟩
  rcases copartner_exists_fam t w hw i with ⟨c, hc⟩
  have hminus : pairChi (w i) c = -1 := circle_pair_minus_one_fam t w hw i c hc
  have hplus : pairChi (w i) c = 1 := by
    rcases hc with ⟨u, hu, j, hj, huj, hg⟩
    have hg2 : c.gcd n = 1 := by
      apply gcd_of_gcd_square_fam (z := c) (n := n)
      rwa [hwi] at hg
    rw [hwi]
    exact pairChi_square (n := n) (y := c) hg2
  rw [hplus] at hminus
  norm_num at hminus

end Apollo
