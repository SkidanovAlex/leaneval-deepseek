/-
Assembly of theorem_1_6: constancy χ₂ = −1 on every coprime tangent pair of
the (−3,5,8,8) packing, and exclusion of square curvatures.

Route (all pieces proven elsewhere):
  * WD (WD.lean): all coprime tangent partners of one circle give one
    Kronecker value ksym · |curvature|  (Prop singleton, per circle).
  * reciprocity (ChiCross + at-most-one-negative): for a coprime tangent pair
    the χ₂ value is symmetric.
  * circle graph connectivity through coprime paths (Copath) then forces χ₂
    to be constant over the whole packing; the base quadruple (−3,5,8,8)
    fixes the constant at −1 (Base).
  * a square curvature has a coprime tangent partner (CrackCopath) and
    Kronecker-square-law forces its χ₂ to be +1 — contradiction.
-/
import Submission.Apollo.WD
import Submission.Apollo.Copath
import Submission.Apollo.Base
import Submission.Apollo.Structure
import Submission.Apollo.OrbitFacts
import Submission.Apollo.CrackCopath
import Submission.Apollo.ChiCross
import Submission.Apollo.Parity
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

/-! ## Ring walks around a circle: symmetric, transitive -/

/-- ring reachability is symmetric (each S-move is an involution). -/
lemma ringReach_symm {i : Fin 4} {w u : Fin 4 → ℤ} (h : ringReach i w u) :
    ringReach i u w := by
  refine rt_symm ?_ h
  intro a b hstep
  rcases hstep with ⟨j, hji, rfl⟩
  refine ⟨j, hji, ?_⟩
  exact (gen_smul_gen_smul a j).symm

/-- ring reachability is transitive. -/
lemma ringReach_trans {i : Fin 4} {a b c : Fin 4 → ℤ} (hab : ringReach i a b)
    (hbc : ringReach i b c) : ringReach i a c :=
  Relation.ReflTransGen.trans hab hbc

/-- the relabelled crack family moves only the coordinates σ 2 and σ 3, so
the circle at coordinate σ 0 is untouched: it is ring-reachable. -/
theorem ringReach_relabelCrack (σ : Equiv.Perm (Fin 4)) (w : Fin 4 → ℤ) (n : ℕ) :
    ringReach (σ 0) w (relabelCrack σ w n) := by
  induction n with
  | zero =>
      change ringReach (σ 0) w w
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      have h2ne : σ 2 ≠ σ 0 := (Equiv.injective σ).ne (by decide : (2 : Fin 4) ≠ 0)
      have h3ne : σ 3 ≠ σ 0 := (Equiv.injective σ).ne (by decide : (3 : Fin 4) ≠ 0)
      have h1 : ringReach (σ 0) w (gen (σ 2) • relabelCrack σ w n) :=
        Relation.ReflTransGen.tail ih ⟨σ 2, h2ne, rfl⟩
      have h2 : ringReach (σ 0) w (gen (σ 3) • (gen (σ 2) • relabelCrack σ w n)) :=
        Relation.ReflTransGen.tail h1 ⟨σ 3, h3ne, rfl⟩
      rw [relabelCrack]
      exact h2

/-- a coprime tangent partner transfers along a ring walk of the quadruple. -/
theorem ringCopartner_of_ringReach {w u : Fin 4 → ℤ} (i : Fin 4)
    (hring : ringReach i w u) (c : ℤ) (hc : RingCopartner w i c) :
    RingCopartner u i c := by
  rcases hc with ⟨v, hwv, j, hji, hvj, hg⟩
  have hui : u i = w i := (formValues_of_ringReach w i u hring).1
  refine ⟨v, ?_, j, hji, hvj, ?_⟩
  · exact ringReach_trans (ringReach_symm hring) hwv
  · rw [hui]
    exact hg

/-! ## The per-circle χ₂ value -/

/-- a coprime tangent partner of the circle at (w,i) exists (crack detour). -/
theorem copartner_exists (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4) :
    ∃ c : ℤ, RingCopartner w i c := by
  let σ : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) i
  have hσ0 : σ 0 = i := by
    dsimp [σ]
    simp
  rcases crack_pair_coprime_exists_at w hw σ with ⟨u, huorb, hun, hfix0, hfix1, z, hz, k, hk, huk⟩
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
  -- ringReach i w u: relabelCrack only moves σ 2, σ 3 and i = σ 0
  rw [← hσ0]
  rcases hun with ⟨n, rfl⟩
  exact ringReach_relabelCrack σ w n

/-- chosen coprime tangent partner of the circle at (w,i). -/
noncomputable def ringPartner (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4) : ℤ :=
  Classical.choose (copartner_exists w hw i)

/-- the intrinsic χ₂ of the circle at (w,i): the Kronecker symbol of any of
its coprime tangent partners against its curvature (well-defined by wd). -/
noncomputable def circleChi (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4) : ℤ :=
  pairChi (w i) (ringPartner w hw i)

/-- the chosen partner really is a coprime tangent partner. -/
lemma ringPartner_spec (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4) :
    RingCopartner w i (ringPartner w hw i) :=
  Classical.choose_spec (copartner_exists w hw i)

/-- circleChi equals the symbol against ANY coprime tangent partner. -/
theorem circleChi_eq_partner (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4)
    {c : ℤ} (hc : RingCopartner w i c) :
    circleChi w hw i = pairChi (w i) c := by
  unfold circleChi
  exact (pairChi_wd w hw i c (ringPartner w hw i) hc (ringPartner_spec w hw i)).symm

/-- circleChi does not depend on the orbit-membership proof. -/
lemma circleChi_irrel (w : Fin 4 → ℤ) (i : Fin 4) {hw hw' : w ∈ apOrbit} :
    circleChi w hw i = circleChi w hw' i := by
  unfold circleChi ringPartner
  exact congrArg (fun h : ∃ c : ℤ, RingCopartner w i c => pairChi (w i) (Classical.choose h))
    (Subsingleton.elim (copartner_exists w hw i) (copartner_exists w hw' i))

/-- circleChi is invariant along ring walks: it depends only on the circle. -/
theorem circleChi_ringReach {w u : Fin 4 → ℤ} (hw : w ∈ apOrbit) (hu : u ∈ apOrbit)
    (i : Fin 4) (hring : ringReach i w u) :
    circleChi w hw i = circleChi u hu i := by
  calc
    circleChi w hw i = pairChi (w i) (ringPartner u hu i) :=
      circleChi_eq_partner w hw i
        (ringCopartner_of_ringReach i (ringReach_symm hring) (ringPartner u hu i) (ringPartner_spec u hu i))
    _ = pairChi (u i) (ringPartner u hu i) := by
      have hui : u i = w i := (formValues_of_ringReach w i u hring).1
      unfold pairChi
      rw [← hui]
    _ = circleChi u hu i := by
      rfl


/-! ## reciprocity on coprime tangent pairs -/

/-- two (distinct) coordinates of a packing quadruple: at least one positive. -/
lemma pos_of_two_coords (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) (i j : Fin 4) (hij : i ≠ j) :
    0 < v i ∨ 0 < v j := by
  by_cases hi : 0 < v i
  · exact Or.inl hi
  · right
    have hine : v i ≠ 0 := orbit_value_ne_zero v hv i
    have hilt : v i < 0 := lt_of_le_of_ne (le_of_not_gt hi) hine
    by_contra hnot
    have hjle : v j ≤ 0 := le_of_not_gt hnot
    have hjne : v j ≠ 0 := orbit_value_ne_zero v hv j
    have hjlt : v j < 0 := lt_of_le_of_ne hjle hjne
    exact apOrbit_at_most_one_neg v hv ⟨i, j, hij, hilt, hjlt⟩

/-- an odd orbit value is ≡ 1 mod 4 (indeed ≡ 5 mod 8). -/
lemma odd_val_four_one (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4)
    (hodd : ¬ 2 ∣ w i) : (w i) % 4 = 1 := by
  have hin : i = 0 ∨ i = 1 := (coord_odd_iff w hw i).1 hodd
  have h5 : w i % 8 = 5 := orbit_odd_coord_eq_five_mod8 w hw i hin
  omega

/-- an odd orbit value is ≡ 5 mod 8. -/
lemma odd_val_eight_five (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4)
    (hodd : ¬ 2 ∣ w i) : (w i) % 8 = 5 := by
  have hin : i = 0 ∨ i = 1 := (coord_odd_iff w hw i).1 hodd
  exact orbit_odd_coord_eq_five_mod8 w hw i hin

/-- coprime integers cannot both be even. -/
lemma not_coprime_of_both_even {x y : ℤ} (hx : 2 ∣ x) (hy : 2 ∣ y) : x.gcd y ≠ 1 := by
  rw [Int.gcd_eq_natAbs]
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simp only [Int.natAbs_mul]
  norm_num
  -- goal: Nat.gcd (2 * a.natAbs) (2 * b.natAbs) ≠ 1
  have hg : Nat.gcd (2 * a.natAbs) (2 * b.natAbs) = 2 * Nat.gcd a.natAbs b.natAbs := by
    rw [Nat.gcd_mul_left]
  rw [hg]
  omega

/-- χ₂ is symmetric on coprime co-occurring pairs (reciprocity). -/
theorem pairChi_symm_tangent (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i j : Fin 4) (hij : i ≠ j)
    (hcop : (w j).gcd (w i) = 1) : pairChi (w i) (w j) = pairChi (w j) (w i) := by
  have hpos : 0 < w i ∨ 0 < w j := pos_of_two_coords w hw i j hij
  by_cases hie : 2 ∣ w i
  · by_cases hje : 2 ∣ w j
    · exfalso
      have hg : (w i).gcd (w j) = 1 := by rwa [Int.gcd_comm] at hcop
      exact not_coprime_of_both_even hie hje hg
    · have hjo5 : (w j) % 8 = 5 := odd_val_eight_five w hw j hje
      exact (pairChi_mixed (o := w j) (e := w i) hjo5 hcop hpos.symm).symm
  · by_cases hje : 2 ∣ w j
    · have hio5 : (w i) % 8 = 5 := odd_val_eight_five w hw i hie
      have hcop' : (w i).gcd (w j) = 1 := by rwa [Int.gcd_comm] at hcop
      exact pairChi_mixed (o := w i) (e := w j) hio5 hcop' hpos
    · have h4i : (w i) % 4 = 1 := odd_val_four_one w hw i hie
      have h4j : (w j) % 4 = 1 := odd_val_four_one w hw j hje
      exact pairChi_odd_odd_symm h4i h4j hpos

/-! ## Prop1step and the occurrence-level χ₂ -/

/-- coprime tangent circles in one packing quadruple have equal χ₂. -/
theorem circleChi_eq_of_coprime_tangent (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i j : Fin 4)
    (hij : i ≠ j) (hcop : (w j).gcd (w i) = 1) :
    circleChi w hw i = circleChi w hw j := by
  calc
    circleChi w hw i = pairChi (w i) (w j) := by
      exact circleChi_eq_partner w hw i ⟨w, Relation.ReflTransGen.refl, j, hij.symm, rfl, hcop⟩
    _ = pairChi (w j) (w i) := pairChi_symm_tangent w hw i j hij hcop
    _ = circleChi w hw j := by
      exact (circleChi_eq_partner w hw j ⟨w, Relation.ReflTransGen.refl, i, hij, rfl,
        (by rwa [Int.gcd_comm] at hcop)⟩).symm

/-- circleChi depends only on the quadruple and index, not on the orbit proof. -/
lemma circleChi_congr {w w' : Fin 4 → ℤ} (hww' : w = w')
    {hw : w ∈ apOrbit} {hw' : w' ∈ apOrbit} (i : Fin 4) :
    circleChi w hw i = circleChi w' hw' i := by
  cases hww'
  exact circleChi_irrel w i

/-- χ₂ at an occurrence. -/
noncomputable def occChi (o : Occ) : ℤ := by
  classical
  exact if ho : valid o then circleChi o.1 ho o.2 else 0

/-- a sameCircle generating step preserves the index. -/
lemma replaceStep_index {o₁ o₂ : Occ} (h : replaceStep o₁ o₂) : o₁.2 = o₂.2 := by
  rcases h with ⟨w, i, j, hne, rfl, rfl⟩
  rfl

/-- χ₂ is invariant under a copath step between valid occurrences. -/
theorem occChi_step {a b : Occ} (hstep : copathStep a b) (ha : valid a) (hb : valid b) :
    occChi a = occChi b := by
  cases a with | mk w i =>
  cases b with | mk u j =>
  unfold occChi
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
    have hmain := circleChi_eq_of_coprime_tangent w ha i j hne hcopW
    calc
      circleChi w ha i = circleChi w ha j := hmain
      _ = circleChi u hb j := by
        exact circleChi_congr hw j
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
      circleChi w ha i = circleChi u hb i := circleChi_ringReach ha hb i hsr
      _ = circleChi u hb j := by rw [hind]

/-- validity is preserved by copath steps. -/
lemma valid_step_of_copathStep {a b : Occ} (hstep : copathStep a b) (ha : valid a) : valid b := by
  rcases hstep with htan | hsame
  · rcases htan with ⟨htan, hcop⟩
    rcases htan with ⟨hw, _⟩
    simpa [valid, hw] using ha
  · exact (sameCircle_valid hsame).1 ha

/-- χ₂ is constant over the connected circle graph. -/
theorem occChi_const (o p : Occ) (ho : valid o) (hp : valid p) : occChi o = occChi p := by
  have hc : copath o p := occ_copath_valid o p ho hp
  have hvp : ∀ b : Occ, copath o b → valid b := by
    intro b hb
    induction hb with
    | refl => exact ho
    | tail hprev hstep ih => exact valid_step_of_copathStep hstep ih
  have hval : ∀ b : Occ, copath o b → occChi o = occChi b := by
    intro b hb
    induction hb with
    | refl => rfl
    | tail hprev hstep ih =>
        exact ih.trans (occChi_step hstep (hvp _ hprev) (valid_step_of_copathStep hstep (hvp _ hprev)))
  exact hval p hc

/-- at the root quadruple the χ₂ value is −1. -/
lemma occChi_base : occChi (q0v, 0) = -1 := by
  unfold occChi
  rw [dif_pos (valid_q0v 0)]
  calc
    circleChi q0v (valid_q0v 0) 0 = pairChi (q0v 0) (q0v 1) := by
      exact circleChi_eq_partner q0v (valid_q0v 0) 0 ⟨q0v, Relation.ReflTransGen.refl,
        (1 : Fin 4), (by decide : (1 : Fin 4) ≠ 0), rfl, (by decide)⟩
    _ = -1 := base_pairChi 0 1 (by decide : (0 : Fin 4) ≠ 1) (by decide)

/-- every coprime tangent partner of any packing circle has χ₂ = −1. -/
theorem circle_pair_minus_one (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4) (c : ℤ)
    (hc : RingCopartner w i c) : pairChi (w i) c = -1 := by
  have hc2 : circleChi w hw i = -1 := by
    calc
      circleChi w hw i = occChi (w, i) := by
        unfold occChi
        rw [dif_pos (show valid (w, i) from hw)]
      _ = occChi (q0v, 0) := occChi_const (w, i) (q0v, 0) hw (valid_q0v 0)
      _ = -1 := occChi_base
  have hc1 : circleChi w hw i = pairChi (w i) c := circleChi_eq_partner w hw i hc
  exact hc1.symm.trans hc2

/-! ## square exclusion -/

/-- coprimality to the square implies coprimality to the base. -/
lemma gcd_of_gcd_square {z n : ℤ} (h : z.gcd (n ^ 2) = 1) : z.gcd n = 1 := by
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

/-- no square curvature occurs in the (−3,5,8,8) packing. -/
theorem no_square_apValues : ∀ n : ℤ, n ^ 2 ∉ apValues := by
  intro n hn
  rcases (mem_apValues_iff.mp hn) with ⟨w, hw, i, hwi⟩
  rcases copartner_exists w hw i with ⟨c, hc⟩
  have hminus : pairChi (w i) c = -1 := circle_pair_minus_one w hw i c hc
  have hplus : pairChi (w i) c = 1 := by
    rcases hc with ⟨u, hu, j, hj, huj, hg⟩
    have hg2 : c.gcd n = 1 := by
      apply gcd_of_gcd_square (z := c) (n := n)
      rwa [hwi] at hg
    rw [hwi]
    exact pairChi_square (n := n) (y := c) hg2
  rw [hplus] at hminus
  norm_num at hminus

end Apollo
