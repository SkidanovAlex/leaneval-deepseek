import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.SmallRank.mulAut_not_dvd_of_abelian_card_dvd_prime_sq
import Submission.Work.LocalPrelim.card_map_mul_card_inf_ker

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.LocalPrelim

open scoped Classical

/-- A subgroup `E` of exponent `p` acts by conjugation on a normal elementary abelian
`p`-subgroup `V` of order at most `p ^ 2`; since the kernel of this action is `E` meet the
centralizer of `V`, and the image is a `p`-subgroup of the automorphism group of `V` (whose
`p`-part is at most `p`, the extreme case being `GL_2(F_p)`), the kernel has index at most `p`.
Suggested ingredients: `Work.SmallRank.card_mulAut_of_exponent_prime_card_prime_sq` and
`Work.SmallRank.prime_sq_not_dvd_mul_prime_sq_sub` handle `|V| = p ^ 2`; `|V| <= p` is easier. -/
theorem card_le_mul_card_inf_centralizer_of_isElementaryAbelian {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {V E : Subgroup X} (hVn : V.Normal)
    (hVel : Work.PGroup.IsElementaryAbelian p V) (hVcard : Nat.card V ≤ p ^ 2)
    (hEel : Work.PGroup.IsElementaryAbelian p E) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓ Subgroup.centralizer (V : Set X)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : V.Normal := hVn
  -- The conjugation action of `X` on the normal subgroup `V`.
  set φ : X →* MulAut ↥V := MulAut.conjNormal with hφ
  -- Step 1: the kernel of `φ` is the centralizer of `V` in `X`.
  have hker : φ.ker = Subgroup.centralizer (V : Set X) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      have h1 : g * h * g⁻¹ = h := by
        have hg' := congrArg (fun (ψ : MulAut ↥V) => (((ψ ⟨h, hh⟩ : ↥V)) : X)) hg
        rw [hφ] at hg'
        simpa using hg'
      calc h * g = (g * h * g⁻¹) * g := by rw [h1]
        _ = g * h := by group
    · intro hg
      ext v
      have hv : (v : X) * g = g * (v : X) := hg v v.2
      rw [hφ, MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← hv, mul_assoc, mul_inv_cancel, mul_one]
  -- Step 2: `|V|` divides `p ^ 2`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp hVel.isPGroup
  have hk2 : k ≤ 2 := by
    have hle : p ^ k ≤ p ^ 2 := by
      rw [← hk]; exact hVcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have hVdvd : Nat.card ↥V ∣ p ^ 2 := by
    rw [hk]; exact pow_dvd_pow p hk2
  -- Step 3: `p ^ 2` does not divide `|Aut V|`.
  have hVcomm : IsMulCommutative ↥V := hVel.comm
  have hnotdvd : ¬ p ^ 2 ∣ Nat.card (MulAut ↥V) :=
    Work.SmallRank.mulAut_not_dvd_of_abelian_card_dvd_prime_sq hp hVcomm hVdvd
  -- Step 4: the image of `E` is a `p`-subgroup of `Aut V`, so its order is `p ^ n`.
  have himgpg : IsPGroup p ↥(E.map φ) := IsPGroup.map hEel.isPGroup φ
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp himgpg
  have hnle : n ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have hdvd : p ^ n ∣ Nat.card (MulAut ↥V) := by
      rw [← hn]; exact Subgroup.card_subgroup_dvd_card _
    exact hnotdvd (dvd_trans (pow_dvd_pow p h2) hdvd)
  have himgle : Nat.card ↥(E.map φ) ≤ p := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hnle with h0 | h1
    · rw [hn, h0]; exact hp.one_lt.le
    · rw [hn, h1]; simp
  -- Step 5: assemble with the first isomorphism theorem.
  have hcard := card_map_mul_card_inf_ker φ E
  rw [hker] at hcard
  calc Nat.card E = Nat.card ↥E := rfl
    _ = Nat.card ↥(E.map φ) * Nat.card ↥(E ⊓ Subgroup.centralizer (V : Set X)) := hcard.symm
    _ ≤ p * Nat.card ↥(E ⊓ Subgroup.centralizer (V : Set X)) :=
        Nat.mul_le_mul_right _ himgle

end Work.LocalPrelim
