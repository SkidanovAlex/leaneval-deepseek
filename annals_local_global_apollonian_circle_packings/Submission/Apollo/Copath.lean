/-
L3: the coprime-path (copath) refinement of tangency edges.

Every tangency edge between two valid occurrences of the packing refines into
a "copath": a sequence of same-circle identifications and coprime tangency
steps (`tangent_copath`).  The proof places the tangent pair at canonical
positions 0,1 by a permutation (`pair_perm_01`), invokes the crack detour
(`CrackCopath.crack_pair_coprime_exists_at`) to add a circle coprime to the
product of the pair, and connects the two occurrences to that circle by
same-circle identifications (`Occurrence.sameCircle_relabelCrack`) and coprime
tangency steps.
-/
import Submission.Apollo.Occurrence
import Submission.Apollo.CrackCopath
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

/-- any ordered pair of distinct indices can be placed at canonical positions
0 and 1 by a permutation. -/
theorem pair_perm_01 (i j : Fin 4) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  fin_cases i <;> fin_cases j
  all_goals (try contradiction)
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨Equiv.swap (1 : Fin 4) 2, by decide, by decide⟩
  · exact ⟨Equiv.swap (1 : Fin 4) 3, by decide, by decide⟩
  · exact ⟨Equiv.swap (0 : Fin 4) 1, by decide, by decide⟩
  · exact ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap (1 : Fin 4) 2, by decide, by decide⟩
  · exact ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap (1 : Fin 4) 3, by decide, by decide⟩
  · exact ⟨Equiv.swap (1 : Fin 4) 0 * Equiv.swap (0 : Fin 4) 2, by decide, by decide⟩
  · exact ⟨Equiv.swap (0 : Fin 4) 2, by decide, by decide⟩
  · exact ⟨Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, by decide, by decide⟩
  · exact ⟨Equiv.swap (1 : Fin 4) 0 * Equiv.swap (0 : Fin 4) 3, by decide, by decide⟩
  · exact ⟨Equiv.swap (0 : Fin 4) 3, by decide, by decide⟩
  · exact ⟨Equiv.swap (0 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2, by decide, by decide⟩

/-- a single copath step from a coprime tangent pair. -/
lemma copath_of_coprime_tangent {o₁ o₂ : Occ} (ht : tangent o₁ o₂)
    (hcop : coprimeValues o₁ o₂) : copath o₁ o₂ :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Or.inl ⟨ht, hcop⟩)

/-- a same-circle step is a copath step. -/
lemma copath_of_sameCircle {o₁ o₂ : Occ} (hs : sameCircle o₁ o₂) : copath o₁ o₂ :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Or.inr hs)

/-- an injective map sends distinct elements to distinct elements. -/
lemma inj_ne {σ : Equiv.Perm (Fin 4)} {a b : Fin 4} (hab : a ≠ b) : σ a ≠ σ b := by
  intro h
  exact hab (σ.injective h)

/-- gcd with a product is 1 implies gcd with a factor is 1. -/
lemma gcd_of_gcd_mul_left {x a b : ℤ} (h : x.gcd (a * b) = 1) : x.gcd a = 1 := by
  by_contra hne
  rcases Nat.exists_prime_and_dvd hne with ⟨p, pp, hpg⟩
  have hgx : p ∣ x.natAbs := by
    rw [Int.gcd_eq_natAbs] at hpg
    exact dvd_trans hpg (Nat.gcd_dvd_left x.natAbs a.natAbs)
  have hga : p ∣ a.natAbs := by
    rw [Int.gcd_eq_natAbs] at hpg
    exact dvd_trans hpg (Nat.gcd_dvd_right x.natAbs a.natAbs)
  have hgab : p ∣ (a * b).natAbs := by
    rw [Int.natAbs_mul]
    simpa [mul_comm] using (dvd_mul_of_dvd_right hga b.natAbs)
  have hpm : p ∣ x.gcd (a * b) := by
    rw [Int.gcd_eq_natAbs]
    exact Nat.dvd_gcd hgx hgab
  have hp1 : p ∣ 1 := by rwa [h] at hpm
  exact pp.not_dvd_one hp1

/-- gcd with a product is 1 implies gcd with the other factor is 1. -/
lemma gcd_of_gcd_mul_right {x a b : ℤ} (h : x.gcd (a * b) = 1) : x.gcd b = 1 := by
  rw [mul_comm] at h
  exact gcd_of_gcd_mul_left h

/-- L3: any tangency edge between valid occurrences refines into a coprime
path. -/
theorem tangent_copath (o₁ o₂ : Occ) (h₁ : valid o₁) (h₂ : valid o₂)
    (ht : tangent o₁ o₂) : copath o₁ o₂ := by
  have hsame : o₁.1 = o₂.1 := ht.1
  have hne : o₁.2 ≠ o₂.2 := ht.2
  let w : Fin 4 → ℤ := o₁.1
  let i : Fin 4 := o₁.2
  let j : Fin 4 := o₂.2
  have hw : w ∈ apOrbit := by simpa [w, valid] using h₁
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
    rcases crack_pair_coprime_exists_at w hw σ with
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




/-- replaceStep preserves validity in both directions. -/
lemma replaceStep_valid_iff {o o' : Occ} (h : replaceStep o o') : valid o ↔ valid o' := by
  rcases h with ⟨w, i, j, hne, rfl, rfl⟩
  constructor
  · intro hw
    exact gen_smul_mem_apOrbit w hw i
  · intro hw'
    have h1 := gen_smul_mem_apOrbit (gen i • w) hw' i
    rwa [gen_smul_gen_smul w i] at h1

/-- a proposition preserved both ways under the generator is preserved under
the generated equivalence relation. -/
lemma eqvGen_iff_preserves {f : Occ → Prop}
    (hstep : ∀ o₁ o₂ : Occ, replaceStep o₁ o₂ → (f o₁ ↔ f o₂))
    {o₁ o₂ : Occ} (h : sameCircle o₁ o₂) : f o₁ ↔ f o₂ := by
  induction h with
  | rel a b hrel => exact hstep a b hrel
  | refl a => exact Iff.rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- same-circle occurrences are valid together. -/
lemma sameCircle_valid {o₁ o₂ : Occ} (h : sameCircle o₁ o₂) : valid o₁ ↔ valid o₂ :=
  eqvGen_iff_preserves (fun o₁ o₂ h => replaceStep_valid_iff h) h

/-- validity is preserved along a connection step. -/
lemma connStep_valid {o₁ o₂ : Occ} (h₁ : valid o₁) (h : connStep o₁ o₂) : valid o₂ := by
  rcases h with h | h
  · rcases h with ⟨hw, _⟩
    change o₂.1 ∈ apOrbit
    rw [← hw]
    exact h₁
  · exact (sameCircle_valid h).1 h₁

/-- validity propagates along a connection path. -/
lemma conn_valid_of_head (a c : Occ) (hva : valid a) (hc : conn a c) : valid c := by
  induction hc with
  | refl => exact hva
  | tail hprev hstep ih =>
      exact connStep_valid ih hstep

/-- a connection step between valid occurrences refines to a copath. -/
lemma copath_of_step {b c : Occ} (hvb : valid b) (hvc : valid c) (hs : connStep b c) :
    copath b c := by
  rcases hs with ht | hsame
  · exact tangent_copath b c hvb hvc ht
  · exact copath_of_sameCircle hsame

/-- L4 (first part): any two valid occurrences are joined by a coprime path. -/
theorem occ_copath_valid (o₁ o₂ : Occ) (h₁ : valid o₁) (h₂ : valid o₂) : copath o₁ o₂ := by
  have aux : ∀ (a c : Occ), valid a → valid c → conn a c → copath a c := by
    intro a c hva hvc hc
    induction hc with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hstep ih =>
        -- validity at the intermediate node, propagated backwards from c:
        have hvb := connStep_valid hvc (connStep_symm hstep)
        exact Relation.ReflTransGen.trans (ih hvb) (copath_of_step hvb hvc hstep)
  exact aux o₁ o₂ h₁ h₂ (occ_conn_valid o₁ o₂ h₁ h₂)

end Apollo
