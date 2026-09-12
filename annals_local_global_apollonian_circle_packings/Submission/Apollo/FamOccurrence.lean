/-
The occurrence/copath layer for the packing of famQuad t: valid occurrences
(w ∈ orbitOf (famQuad t)), connectedness of the circle graph, and refinement
of tangency edges into coprime paths.

(Family analogue of Occurrence.occ_conn_valid and Copath.occ_copath_valid.)
-/
import Submission.Apollo.FamOrbit
import Submission.Apollo.FamCrack
import Submission.Apollo.Occurrence
import Submission.Apollo.Copath
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

/-- an occurrence is family-valid when its quadruple lies in the family orbit. -/
def famValid (t : ℕ) (o : Occ) : Prop := o.1 ∈ orbitOf (famQuad t)

/-- family validity at a family-orbit quadruple. -/
lemma famValid_of_quad (t : ℕ) {w : Fin 4 → ℤ} (hw : w ∈ orbitOf (famQuad t)) (i : Fin 4) :
    famValid t (w, i) := by
  exact hw

/-- family validity is preserved by the S-moves. -/
lemma famValid_move (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) (i : Fin 4) :
    famValid t (gen i • w, i) := by
  dsimp [famValid]
  exact famOrbit_gen t w hw i

/-- The circle graph of the family packing is connected: every family-valid
occurrence is connected to the occurrence (famQuad t, 0). -/
theorem fam_occ_conn_base (t : ℕ) (o : Occ) (ho : famValid t o) : conn o (famQuad t, 0) := by
  let P : (Fin 4 → ℤ) → Prop := fun w => ∀ i : Fin 4, conn (w, i) (famQuad t, 0)
  have hP : P (famQuad t) := by
    intro i
    by_cases hi : i = 0
    · subst i
      exact Relation.ReflTransGen.refl
    · exact tangent_conn (tangent_self (w := famQuad t) (i := i) (j := 0) hi)
  have hS : ∀ i : Fin 4, ∀ w : Fin 4 → ℤ, P w → P (gen i • w) := by
    intro i w hw k
    by_cases hki : k = i
    · subst k
      rcases (exists_ne i : ∃ j : Fin 4, j ≠ i) with ⟨j, hji⟩
      apply Relation.ReflTransGen.trans (b := (w, j))
      · exact new_circle_reaches_old w i j hji
      · exact hw j
    · have hik : i ≠ k := by
        intro hik
        exact hki hik.symm
      apply Relation.ReflTransGen.trans (b := (w, k))
      · exact sameCircle_conn (sameCircle_move' i k hik)
      · exact hw k
  have hall := of_orbitOf_apply (w0 := famQuad t) (P := P) hP hS o.1 ho
  exact hall o.2

/-- any two family-valid occurrences are connected. -/
theorem fam_occ_conn_valid (t : ℕ) (o₁ o₂ : Occ) (h₁ : famValid t o₁) (h₂ : famValid t o₂) :
    conn o₁ o₂ := by
  apply Relation.ReflTransGen.trans (b := (famQuad t, 0))
  · exact fam_occ_conn_base t o₁ h₁
  · exact conn_symm (fam_occ_conn_base t o₂ h₂)

/-- replaceStep preserves family validity in both directions. -/
lemma fam_replaceStep_valid_iff (t : ℕ) {o o' : Occ} (h : replaceStep o o') :
    famValid t o ↔ famValid t o' := by
  rcases h with ⟨w, i, j, hne, rfl, rfl⟩
  constructor
  · intro hw
    exact famOrbit_gen t w hw i
  · intro hw'
    have h1 := famOrbit_gen t (gen i • w) hw' i
    rwa [gen_smul_gen_smul w i] at h1

/-- same-circle occurrences are family-valid together. -/
lemma fam_sameCircle_valid (t : ℕ) {o₁ o₂ : Occ} (h : sameCircle o₁ o₂) :
    famValid t o₁ ↔ famValid t o₂ :=
  eqvGen_iff_preserves (fun o₁ o₂ h => fam_replaceStep_valid_iff t h) h

/-- family validity is preserved along a connection step. -/
lemma fam_connStep_valid (t : ℕ) {o₁ o₂ : Occ} (h₁ : famValid t o₁) (h : connStep o₁ o₂) :
    famValid t o₂ := by
  rcases h with h | h
  · rcases h with ⟨hw, _⟩
    change o₂.1 ∈ orbitOf (famQuad t)
    rw [← hw]
    exact h₁
  · exact (fam_sameCircle_valid t h).1 h₁

/-- family validity propagates along a connection path. -/
lemma fam_conn_valid_of_head (t : ℕ) (a c : Occ) (hva : famValid t a) (hc : conn a c) :
    famValid t c := by
  induction hc with
  | refl => exact hva
  | tail hprev hstep ih =>
      exact fam_connStep_valid t ih hstep

/-- L3 (family): any tangency edge between family-valid occurrences refines
into a coprime path. -/
theorem fam_tangent_copath (t : ℕ) (o₁ o₂ : Occ) (h₁ : famValid t o₁) (h₂ : famValid t o₂)
    (ht : tangent o₁ o₂) : copath o₁ o₂ := by
  have hsame : o₁.1 = o₂.1 := ht.1
  have hne : o₁.2 ≠ o₂.2 := ht.2
  let w : Fin 4 → ℤ := o₁.1
  let i : Fin 4 := o₁.2
  let j : Fin 4 := o₂.2
  have hw : w ∈ orbitOf (famQuad t) := by simpa [w, famValid] using h₁
  have ho1 : o₁ = (w, i) := by
    apply Prod.ext <;> rfl
  have ho2 : o₂ = (w, j) := by
    apply Prod.ext
    · simpa [w] using hsame.symm
    · rfl
  by_cases hcop : (w i).gcd (w j) = 1
  · have ht' : tangent (w, i) (w, j) := by
      dsimp [tangent]
      exact ⟨rfl, by simpa [i, j] using hne⟩
    have hc' : coprimeValues (w, i) (w, j) := by
      dsimp [coprimeValues, ovalue]
      exact hcop
    have hp : copath (w, i) (w, j) := copath_of_coprime_tangent ht' hc'
    rw [ho1, ho2]
    exact hp
  · have hi : i ≠ j := by simpa [i, j] using hne
    rcases pair_perm_01 i j hi with ⟨σ, hσ0, hσ1⟩
    rcases crack_pair_coprime_exists_at_fam t w hw σ with
      ⟨u, hu, ⟨n, hun⟩, huf0, huf1, z, hz, k, hk, huk⟩
    have hik : i ≠ k := by
      rcases hk with hk2 | hk3
      · rw [← hσ0, hk2]
        exact inj_ne (by decide : (0 : Fin 4) ≠ 2)
      · rw [← hσ0, hk3]
        exact inj_ne (by decide : (0 : Fin 4) ≠ 3)
    have hkj : k ≠ j := by
      rcases hk with hk2 | hk3
      · rw [hk2, ← hσ1]
        exact inj_ne (by decide : (2 : Fin 4) ≠ 1)
      · rw [hk3, ← hσ1]
        exact inj_ne (by decide : (3 : Fin 4) ≠ 1)
    have hs1 : sameCircle (w, i) (u, i) := by
      rw [← hσ0, hun]
      exact sameCircle_relabelCrack σ w n (σ 0)
        (inj_ne (by decide : (0 : Fin 4) ≠ 2)) (inj_ne (by decide : (0 : Fin 4) ≠ 3))
    have hs4 : sameCircle (u, j) (w, j) := by
      rw [← hσ1, hun]
      exact Relation.EqvGen.symm (w, σ 1) (relabelCrack σ w n, σ 1)
        (sameCircle_relabelCrack σ w n (σ 1)
          (inj_ne (by decide : (1 : Fin 4) ≠ 2)) (inj_ne (by decide : (1 : Fin 4) ≠ 3)))
    have hcopik : coprimeValues (u, i) (u, k) := by
      dsimp [coprimeValues, ovalue]
      rw [← hσ0, huf0, huk]
      rw [Int.gcd_comm]
      exact gcd_of_gcd_mul_left hz
    have htanik : tangent (u, i) (u, k) := by
      dsimp [tangent]
      exact ⟨rfl, hik⟩
    have hcopkj : coprimeValues (u, k) (u, j) := by
      dsimp [coprimeValues, ovalue]
      rw [← hσ1, huf1, huk]
      exact gcd_of_gcd_mul_right hz
    have htankj : tangent (u, k) (u, j) := by
      dsimp [tangent]
      exact ⟨rfl, hkj⟩
    have p1 : copath (w, i) (u, i) := copath_of_sameCircle hs1
    have p2 : copath (u, i) (u, k) := copath_of_coprime_tangent htanik hcopik
    have p3 : copath (u, k) (u, j) := copath_of_coprime_tangent htankj hcopkj
    have p4 : copath (u, j) (w, j) := copath_of_sameCircle hs4
    have p12 : copath (w, i) (u, k) := Relation.ReflTransGen.trans p1 p2
    have p123 : copath (w, i) (u, j) := Relation.ReflTransGen.trans p12 p3
    have p1234 : copath (w, i) (w, j) := Relation.ReflTransGen.trans p123 p4
    rw [ho1, ho2]
    exact p1234

/-- a connection step between family-valid occurrences refines to a copath. -/
lemma fam_copath_of_step (t : ℕ) {b c : Occ} (hvb : famValid t b) (hvc : famValid t c)
    (hs : connStep b c) : copath b c := by
  rcases hs with ht | hsame
  · exact fam_tangent_copath t b c hvb hvc ht
  · exact copath_of_sameCircle hsame

/-- L4 (family): any two family-valid occurrences are joined by a coprime
path. -/
theorem fam_occ_copath_valid (t : ℕ) (o₁ o₂ : Occ) (h₁ : famValid t o₁) (h₂ : famValid t o₂) :
    copath o₁ o₂ := by
  have aux : ∀ (a c : Occ), famValid t a → famValid t c → conn a c → copath a c := by
    intro a c hva hvc hc
    induction hc with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hstep ih =>
        have hvb := fam_connStep_valid t hvc (connStep_symm hstep)
        exact Relation.ReflTransGen.trans (ih hvb) (fam_copath_of_step t hvb hvc hstep)
  exact aux o₁ o₂ h₁ h₂ (fam_occ_conn_valid t o₁ o₂ h₁ h₂)

end Apollo
