import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Submission.NK.TameStructureDeep.Tame.TameClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-! ## A group-theoretic lemma: two roots of the same element are captured by one

If `u ^ n₁ = v ^ n₂ = c` in a commutative group and `n₁`, `n₂` are nonzero, there is a single
`n` (namely `n₁ * n₂ / gcd n₁ n₂`) and an element `w` with `w ^ n = c` such that `u` and `v` are
both `w`-powers up to an `n₁`- (resp. `n₂`-)th root of unity.  Concretely, with
`m₁ = n₂ / gcd n₁ n₂`, `m₂ = n₁ / gcd n₁ n₂` (so that `m₁` and `m₂` are coprime and
`m₁ * n₁ = m₂ * n₂ = n`), and Bézout coefficients `a m₁ + b m₂ = 1`, one takes
`w = u ^ a * v ^ b`; then `w ^ n = c ^ (a m₁ + b m₂) = c`. -/
private lemma group_root_data {G : Type*} [CommGroup G] {u v c : G} {n₁ n₂ : ℕ}
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (h₁ : u ^ n₁ = c) (h₂ : v ^ n₂ = c) :
    ∃ (n m₁ m₂ : ℕ) (w ζ₁ ζ₂ : G), n = m₁ * n₁ ∧ n = m₂ * n₂ ∧ n ∣ n₁ * n₂ ∧
      w ^ n = c ∧ ζ₁ ^ n₁ = 1 ∧ ζ₂ ^ n₂ = 1 ∧ u = w ^ m₁ * ζ₁ ∧ v = w ^ m₂ * ζ₂ := by
  have hgpos : 0 < n₁.gcd n₂ := Nat.gcd_pos_of_pos_left n₂ (Nat.pos_of_ne_zero hn₁)
  have hg₁ : n₁.gcd n₂ ∣ n₁ := Nat.gcd_dvd_left n₁ n₂
  have hg₂ : n₁.gcd n₂ ∣ n₂ := Nat.gcd_dvd_right n₁ n₂
  have hcop : (n₂ / n₁.gcd n₂).Coprime (n₁ / n₁.gcd n₂) :=
    (Nat.coprime_div_gcd_div_gcd (m := n₁) (n := n₂) hgpos).symm
  obtain ⟨a, b, hbez⟩ : ∃ a b : ℤ, a * ((n₂ / n₁.gcd n₂ : ℕ) : ℤ) +
      b * ((n₁ / n₁.gcd n₂ : ℕ) : ℤ) = 1 := by
    refine ⟨(n₂ / n₁.gcd n₂).gcdA (n₁ / n₁.gcd n₂),
      (n₂ / n₁.gcd n₂).gcdB (n₁ / n₁.gcd n₂), ?_⟩
    have h := Nat.gcd_eq_gcd_ab (n₂ / n₁.gcd n₂) (n₁ / n₁.gcd n₂)
    rw [show (n₂ / n₁.gcd n₂).gcd (n₁ / n₁.gcd n₂) = 1 from hcop] at h
    have h' : ((n₂ / n₁.gcd n₂ : ℕ) : ℤ) * ((n₂ / n₁.gcd n₂).gcdA (n₁ / n₁.gcd n₂)) +
        ((n₁ / n₁.gcd n₂ : ℕ) : ℤ) * ((n₂ / n₁.gcd n₂).gcdB (n₁ / n₁.gcd n₂)) = 1 := by
      simpa using h.symm
    rw [mul_comm ((n₂ / n₁.gcd n₂).gcdA (n₁ / n₁.gcd n₂)) ((n₂ / n₁.gcd n₂ : ℕ) : ℤ),
        mul_comm ((n₂ / n₁.gcd n₂).gcdB (n₁ / n₁.gcd n₂)) ((n₁ / n₁.gcd n₂ : ℕ) : ℤ)]
    exact h'
  have hm₁ : n₁ * (n₂ / n₁.gcd n₂) = n₁ * n₂ / n₁.gcd n₂ :=
    (Nat.mul_div_assoc n₁ hg₂).symm
  have hm₂ : n₂ * (n₁ / n₁.gcd n₂) = n₁ * n₂ / n₁.gcd n₂ := by
    have h := (Nat.mul_div_assoc n₂ hg₁).symm
    rw [Nat.mul_comm n₂ n₁] at h
    exact h
  have hm₁' : (n₂ / n₁.gcd n₂) * n₁ = n₁ * n₂ / n₁.gcd n₂ := by
    rw [Nat.mul_comm (n₂ / n₁.gcd n₂) n₁, hm₁]
  have hm₂' : (n₁ / n₁.gcd n₂) * n₂ = n₁ * n₂ / n₁.gcd n₂ := by
    rw [Nat.mul_comm (n₁ / n₁.gcd n₂) n₂, hm₂]
  set w := u ^ a * v ^ b with hwdef
  have hwpowZ : w ^ ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ) = c := by
    have e₁ : ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ) = ((n₂ / n₁.gcd n₂ : ℕ) : ℤ) * (n₁ : ℤ) := by
      rw [← hm₁]; push_cast; ring
    have e₂ : ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ) = ((n₁ / n₁.gcd n₂ : ℕ) : ℤ) * (n₂ : ℤ) := by
      rw [← hm₂]; push_cast; ring
    have hz₁ : u ^ (n₁ : ℤ) = c := by rw [zpow_natCast]; exact h₁
    have hz₂ : v ^ (n₂ : ℤ) = c := by rw [zpow_natCast]; exact h₂
    calc w ^ ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ)
        = (u ^ a * v ^ b) ^ ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ) := by rw [hwdef]
      _ = (u ^ a) ^ ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ) *
            (v ^ b) ^ ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ) := by rw [mul_zpow]
      _ = u ^ (a * ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ)) *
            v ^ (b * ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ)) := by
          rw [← zpow_mul u a _, ← zpow_mul v b _]
      _ = u ^ ((a * ((n₂ / n₁.gcd n₂ : ℕ) : ℤ)) * (n₁ : ℤ)) *
            v ^ ((b * ((n₁ / n₁.gcd n₂ : ℕ) : ℤ)) * (n₂ : ℤ)) := by
          rw [show a * ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ) =
                (a * ((n₂ / n₁.gcd n₂ : ℕ) : ℤ)) * (n₁ : ℤ) by rw [e₁]; ring,
              show b * ((n₁ * n₂ / n₁.gcd n₂ : ℕ) : ℤ) =
                (b * ((n₁ / n₁.gcd n₂ : ℕ) : ℤ)) * (n₂ : ℤ) by rw [e₂]; ring]
      _ = (u ^ (n₁ : ℤ)) ^ (a * ((n₂ / n₁.gcd n₂ : ℕ) : ℤ)) *
            (v ^ (n₂ : ℤ)) ^ (b * ((n₁ / n₁.gcd n₂ : ℕ) : ℤ)) := by
          rw [zpow_mul' u (a * ((n₂ / n₁.gcd n₂ : ℕ) : ℤ)) (n₁ : ℤ),
              zpow_mul' v (b * ((n₁ / n₁.gcd n₂ : ℕ) : ℤ)) (n₂ : ℤ)]
      _ = c ^ (a * ((n₂ / n₁.gcd n₂ : ℕ) : ℤ)) *
            c ^ (b * ((n₁ / n₁.gcd n₂ : ℕ) : ℤ)) := by rw [hz₁, hz₂]
      _ = c ^ (a * ((n₂ / n₁.gcd n₂ : ℕ) : ℤ) + b * ((n₁ / n₁.gcd n₂ : ℕ) : ℤ)) := by
          rw [zpow_add]
      _ = c := by rw [hbez, zpow_one]
  have hwpow : w ^ (n₁ * n₂ / n₁.gcd n₂) = c := by
    rw [← zpow_natCast]; exact hwpowZ
  have hζ₁pow : (u * (w ^ (n₂ / n₁.gcd n₂))⁻¹) ^ n₁ = 1 := by
    have hw : (w ^ (n₂ / n₁.gcd n₂)) ^ n₁ = c := by
      rw [← pow_mul, hm₁', hwpow]
    rw [mul_pow, inv_pow, hw, h₁, mul_inv_cancel]
  have hζ₂pow : (v * (w ^ (n₁ / n₁.gcd n₂))⁻¹) ^ n₂ = 1 := by
    have hw : (w ^ (n₁ / n₁.gcd n₂)) ^ n₂ = c := by
      rw [← pow_mul, hm₂', hwpow]
    rw [mul_pow, inv_pow, hw, h₂, mul_inv_cancel]
  have hu : u = w ^ (n₂ / n₁.gcd n₂) * (u * (w ^ (n₂ / n₁.gcd n₂))⁻¹) := by
    rw [mul_comm (w ^ (n₂ / n₁.gcd n₂)) (u * (w ^ (n₂ / n₁.gcd n₂))⁻¹),
      mul_assoc, inv_mul_cancel, mul_one]
  have hv : v = w ^ (n₁ / n₁.gcd n₂) * (v * (w ^ (n₁ / n₁.gcd n₂))⁻¹) := by
    rw [mul_comm (w ^ (n₁ / n₁.gcd n₂)) (v * (w ^ (n₁ / n₁.gcd n₂))⁻¹),
      mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨n₁ * n₂ / n₁.gcd n₂, n₂ / n₁.gcd n₂, n₁ / n₁.gcd n₂, w,
      u * (w ^ (n₂ / n₁.gcd n₂))⁻¹, v * (w ^ (n₁ / n₁.gcd n₂))⁻¹,
      ?_, ?_, ?_, hwpow, hζ₁pow, hζ₂pow, hu, hv⟩
  · rw [Nat.mul_comm (n₂ / n₁.gcd n₂) n₁, hm₁]
  · rw [Nat.mul_comm (n₁ / n₁.gcd n₂) n₂, hm₂]
  · exact ⟨n₁.gcd n₂, (Nat.div_mul_cancel (hg₁.trans (Nat.dvd_mul_right n₁ n₂))).symm⟩

/-- **Every root of unity of order prime to `p` lies in `κ^{ur} = κ(μ_{p'})`.**

If `ζ ^ m = 1` and `p ∤ m`, then `ζ` is a root of unity whose order divides `m`, hence is prime
to `p`, so `ζ` generates one of the layers `κ⟮ζ⟯` defining the unramified closure. -/
private lemma mem_unramifiedClosure_of_pow_eq_one' {p m : ℕ} (hm : ¬ p ∣ m) {ζ : K'}
    (hζ : ζ ^ m = 1) :
    ζ ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p := by
  have hdvd : orderOf ζ ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hζ
  have hne : ¬ p ∣ orderOf ζ := fun h => hm (h.trans hdvd)
  exact NK.TameStructureDeep.mem_unramifiedClosure_of_isPrimitiveRoot (κ := κ) (K' := K')
    hne (IsPrimitiveRoot.iff_orderOf.mpr rfl)

theorem exists_root_capturing_pair {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    {p : ℕ} (hp : p.Prime) {π β₁ β₂ : K'} {n₁ n₂ : ℕ}
    (hn₁ : ¬ p ∣ n₁) (hn₂ : ¬ p ∣ n₂) (h₁ : β₁ ^ n₁ = π) (h₂ : β₂ ^ n₂ = π) :
    ∃ (n : ℕ) (β : K'), ¬ p ∣ n ∧ β ^ n = π ∧
      β₁ ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p ⊔
        IntermediateField.adjoin κ ({β} : Set K') ∧
      β₂ ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p ⊔
        IntermediateField.adjoin κ ({β} : Set K') := by
  classical
  by_cases hπ : π = 0
  · refine ⟨1, 0, hp.not_dvd_one, ?_, ?_, ?_⟩
    · simp [hπ]
    · have hb : β₁ = 0 := by
        by_contra hb
        exact pow_ne_zero n₁ hb (by rw [h₁, hπ])
      rw [hb]; exact zero_mem _
    · have hb : β₂ = 0 := by
        by_contra hb
        exact pow_ne_zero n₂ hb (by rw [h₂, hπ])
      rw [hb]; exact zero_mem _
  have hn₁0 : n₁ ≠ 0 := fun h => hn₁ (by rw [h]; exact dvd_zero p)
  have hn₂0 : n₂ ≠ 0 := fun h => hn₂ (by rw [h]; exact dvd_zero p)
  have hβ₁ne : β₁ ≠ 0 := fun h => hπ (by rw [← h₁, h, zero_pow hn₁0])
  have hβ₂ne : β₂ ≠ 0 := fun h => hπ (by rw [← h₂, h, zero_pow hn₂0])
  obtain ⟨n, m₁, m₂, w, ζ₁, ζ₂, hn_eq₁, hn_eq₂, hndvd, hwpow, hζ₁pow, hζ₂pow, hu, hv⟩ :=
    group_root_data (u := Units.mk0 β₁ hβ₁ne) (v := Units.mk0 β₂ hβ₂ne)
      (c := Units.mk0 π hπ) hn₁0 hn₂0 (by ext; simpa using h₁) (by ext; simpa using h₂)
  refine ⟨n, (w : K'), ?_, ?_, ?_, ?_⟩
  · intro hd
    rcases (hp.dvd_mul).mp (hd.trans hndvd) with h | h
    · exact hn₁ h
    · exact hn₂ h
  · have hh := congrArg (fun x : K'ˣ => (x : K')) hwpow
    simpa using hh
  · have heq : β₁ = (w : K') ^ m₁ * (ζ₁ : K') := by
      have hh := congrArg (fun x : K'ˣ => (x : K')) hu
      simpa using hh
    have hζ₁mem : (ζ₁ : K') ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p := by
      refine mem_unramifiedClosure_of_pow_eq_one' hn₁ ?_
      have hh := congrArg (fun x : K'ˣ => (x : K')) hζ₁pow
      simpa using hh
    rw [heq]
    refine mul_mem ?_ ?_
    · exact pow_mem (SetLike.le_def.mp le_sup_right
        (IntermediateField.mem_adjoin_simple_self κ (w : K'))) m₁
    · exact SetLike.le_def.mp le_sup_left hζ₁mem
  · have heq : β₂ = (w : K') ^ m₂ * (ζ₂ : K') := by
      have hh := congrArg (fun x : K'ˣ => (x : K')) hv
      simpa using hh
    have hζ₂mem : (ζ₂ : K') ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p := by
      refine mem_unramifiedClosure_of_pow_eq_one' hn₂ ?_
      have hh := congrArg (fun x : K'ˣ => (x : K')) hζ₂pow
      simpa using hh
    rw [heq]
    refine mul_mem ?_ ?_
    · exact pow_mem (SetLike.le_def.mp le_sup_right
        (IntermediateField.mem_adjoin_simple_self κ (w : K'))) m₂
    · exact SetLike.le_def.mp le_sup_left hζ₂mem

end NK.TameStructureDeep.Tame
