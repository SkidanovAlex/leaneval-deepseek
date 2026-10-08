import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sec5Fix.prop2b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.Sec5Fix.NF

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Peterfalvi I Ch. III §5 Prop. 3, counting step

Let `N = O_{f'}(M)` be the non-trivial subgroup of §5 Prop. 2 (d) (`f = orderOf (u*t) ∈ {3,5}`).
The source argues: *"suppose `C_H(N)` has only one or two fixed points in `Ω`. By Prop. 2 (d)
`N ≠ 1`. If `x ∈ N#`, `x` has odd order and centralises `C_H(N)`, so it fixes the fixed point(s)
of `C_H(N)`. This contradicts Prop. 2 (b)."*

Formally the counting is: `x` permutes `fixedPts H (C_H(N))` (it centralises `C_H(N)`), so by the
pigeonhole applied to `ω₀, x•ω₀, x²•ω₀` (three points of a set of at most two elements) one of
`x`, `x²` fixes the base point `ω₀`, i.e. `x ∈ H` or `x² ∈ H`; as `orderOf x` is odd, `x² ∈ H`
forces `x ∈ H`. But `fix(⟨x⟩) = ∅` (the hypothesis `hB`, = §5 Prop. 2 (b)), so `x ∉ H`: absurd.

This isolates the counting step; it is consumed by `Sec5Fix.normFitting`. -/

theorem three_le_fixedPts_centH
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5)
    (hB : (∀ x ∈ Work.NormalComplement.Design.Mset u t, x ≠ 1 →
        Submission.Blueprint.fixedPts H (Subgroup.zpowers x) = ∅) ∧
      Nat.Coprime (Work.NormalComplement.Design.Mset u t).ncard
        (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))))
    (M : Subgroup G) (hM : (M : Set G) = Work.NormalComplement.Design.Mset u t)
    (hMd : Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M ≠ ⊥) :
    3 ≤ (Submission.Blueprint.fixedPts H
      ((Subgroup.centralizer
        ((Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Subgroup G) : Set G)) ⊓ H)).ncard := by
  classical
  -- `X = C_H(N)` with `N = O_{f'}(M)`.
  set X : Subgroup G :=
    Subgroup.centralizer ((Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Subgroup G) : Set G) ⊓ H
    with hXdef
  -- choose `x ∈ N#`
  obtain ⟨x, hxN, hx1⟩ :
      ∃ x ∈ Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M, x ≠ 1 := by
    by_contra hc
    have hc' : ∀ x ∈ Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M, x = 1 := by
      intro x hx
      by_contra hx1
      exact hc ⟨x, hx, hx1⟩
    exact hMd (Subgroup.eq_bot_iff_forall _ |>.mpr hc')
  have hxM : x ∈ M := Subgroup.map_subtype_le _ hxN
  have hxMset : x ∈ Work.NormalComplement.Design.Mset u t := by rw [← hM]; exact hxM
  have hxinv : t * x * t⁻¹ = x⁻¹ := hxMset.2
  have hxut : x ∈ Subgroup.centralizer ({u * t} : Set G) := hxMset.1
  have hxfix : fixedPts H (Subgroup.zpowers x) = ∅ := hB.1 x hxMset hx1
  -- `x` fixes no point of `Ω`, hence `x ∉ H`
  have hxnotH : x ∉ H := by
    intro hxH
    have hmem : Work.DoubleTransitivity.pt H ∈ fixedPts H (Subgroup.zpowers x) := by
      rw [Work.DoubleTransitivity.pt_mem_fixedPts_iff]
      exact Subgroup.zpowers_le.mpr hxH
    rw [hxfix] at hmem
    exact hmem
  -- `V = centD H t = C_G(t) ⊓ C_G(ut)`
  have hCentD : Submission.Blueprint.centD H t =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({u * t} : Set G) :=
    Work.NormalComplement.Sec5Fix.centD_eq_inf_centralizer_mul h.se hu.1 hu.2.1 hu.2.2
  -- ## `x` has odd order
  -- (if `x` had even order, `x ^ k` (`2 * k = orderOf x`) would be an involution of `V`
  -- centralised by `t`, whence `t ∈ H` by strong embeddedness)
  have hxodd : Odd (orderOf x) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    obtain ⟨k, hk0⟩ := heven
    have hk : orderOf x = 2 * k := by rw [hk0, two_mul]
    have h2le : 2 ≤ orderOf x := by
      have h0 : 0 < orderOf x := Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard x) Nat.card_pos
      have h1 : orderOf x ≠ 1 := fun hh => hx1 (orderOf_eq_one_iff.mp hh)
      omega
    have hkpos : 1 ≤ k := by rw [hk] at h2le; omega
    set y : G := x ^ k with hy
    have hyne : y ≠ 1 := by
      intro hy1
      have hdvd : orderOf x ∣ k := orderOf_dvd_iff_pow_eq_one.mpr (by rw [← hy]; exact hy1)
      rw [hk] at hdvd
      have hle : 2 * k ≤ k := Nat.le_of_dvd (by omega) hdvd
      omega
    have hy2' : y ^ 2 = 1 := by
      rw [hy, ← pow_mul, show k * 2 = 2 * k from by omega, ← hk, pow_orderOf_eq_one]
    have hy2 : orderOf y = 2 := by
      have hdvd2 : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2'
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) hyne
      · exact hh
    have hymul : y * y = 1 := by rw [← pow_two]; exact hy2'
    have hyinvself : y⁻¹ = y := inv_eq_of_mul_eq_one_right hymul
    -- `t` inverts `y`, so `t` centralises the involution `y`
    have htinv : t * y * t⁻¹ = y⁻¹ := by
      have hconj : ∀ n : ℕ, t * x ^ n * t⁻¹ = (t * x * t⁻¹) ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, pow_succ, ← ih]; group
      rw [hy, hconj k, hxinv, inv_pow]
    -- `y ∈ V`
    have hycent : y ∈ Submission.Blueprint.centD H t := by
      rw [hCentD]
      refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.pow_mem _ hxut k⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y * t = (t * y * t⁻¹) * t := by rw [htinv, hyinvself]
        _ = t * y := by group
    have hyH : y ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hycent).1).1
    have htcent : t ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * y = (t * y * t⁻¹) * t := by group
        _ = y * t := by rw [htinv, hyinvself]
    have h2y : 2 ∣ orderOf y := by rw [hy2]
    have hCle := Work.ThreePoints.IsStronglyEmbedded.centralizer_le h.se hyH h2y
    exact h.notMem (hCle htcent)
  -- ## the counting argument
  by_contra hcon
  have hle : (fixedPts H X).ncard ≤ 2 := by
    have := Nat.lt_of_not_le hcon
    omega
  -- `x` centralises `X`
  have hcommX : ∀ y ∈ X, y * x = x * y := by
    intro y hy
    have hyC : y ∈ Subgroup.centralizer
        ((Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hy).1
    exact (Subgroup.mem_centralizer_iff.mp hyC x hxN).symm
  -- `x` maps `fixedPts H X` into itself
  have hsmul_mem : ∀ ω ∈ fixedPts H X, x • ω ∈ fixedPts H X := by
    intro ω hω
    rw [Work.ThreePoints.mem_fixedPts] at hω ⊢
    intro y hy
    have hyx : x⁻¹ * y * x ∈ X := by
      have h1 : x⁻¹ * y * x = y := by
        rw [mul_assoc, hcommX y hy, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h1]; exact hy
    calc y • (x • ω) = (y * x) • ω := (mul_smul y x ω).symm
      _ = (x * (x⁻¹ * y * x)) • ω := by rw [show y * x = x * (x⁻¹ * y * x) from by group]
      _ = x • ((x⁻¹ * y * x) • ω) := mul_smul x (x⁻¹ * y * x) ω
      _ = x • ω := by rw [hω (x⁻¹ * y * x) hyx]
  have hω0 : Work.DoubleTransitivity.pt H ∈ fixedPts H X := by
    rw [Work.DoubleTransitivity.pt_mem_fixedPts_iff]
    exact inf_le_right
  have hω1 : x • Work.DoubleTransitivity.pt H ∈ fixedPts H X := hsmul_mem _ hω0
  have hω2 : x ^ 2 • Work.DoubleTransitivity.pt H ∈ fixedPts H X := by
    rw [pow_two, mul_smul]
    exact hsmul_mem _ hω1
  -- three points in a set of at most two elements
  have hpair : Work.DoubleTransitivity.pt H = x • Work.DoubleTransitivity.pt H ∨
      Work.DoubleTransitivity.pt H = x ^ 2 • Work.DoubleTransitivity.pt H ∨
      x • Work.DoubleTransitivity.pt H = x ^ 2 • Work.DoubleTransitivity.pt H := by
    by_contra hc
    have h01 : Work.DoubleTransitivity.pt H ≠ x • Work.DoubleTransitivity.pt H :=
      fun hh => hc (Or.inl hh)
    have h02 : Work.DoubleTransitivity.pt H ≠ x ^ 2 • Work.DoubleTransitivity.pt H :=
      fun hh => hc (Or.inr (Or.inl hh))
    have h12 : x • Work.DoubleTransitivity.pt H ≠ x ^ 2 • Work.DoubleTransitivity.pt H :=
      fun hh => hc (Or.inr (Or.inr hh))
    have h2 : 2 < (fixedPts H X).ncard :=
      (Set.two_lt_ncard (s := fixedPts H X) (Set.toFinite _)).mpr
        ⟨_, hω0, _, hω1, _, hω2, h01, h02, h12⟩
    omega
  have hx2H : x ^ 2 ∈ H := by
    have key1 : x • Work.DoubleTransitivity.pt H = Work.DoubleTransitivity.pt H → x ^ 2 ∈ H := by
      intro hh
      have hxH : x ∈ H := by
        have h2 := (Work.DoubleTransitivity.smul_mk_eq_mk_iff (H := H)).mp hh
        rwa [Work.DoubleTransitivity.conj_one] at h2
      exact Subgroup.pow_mem _ hxH 2
    have key2 : x ^ 2 • Work.DoubleTransitivity.pt H = Work.DoubleTransitivity.pt H → x ^ 2 ∈ H := by
      intro hh
      have h2 := (Work.DoubleTransitivity.smul_mk_eq_mk_iff (H := H)).mp hh
      rwa [Work.DoubleTransitivity.conj_one] at h2
    rcases hpair with hh | hh | hh
    · exact key1 hh.symm
    · exact key2 hh.symm
    · refine key1 ?_
      have h2 := congrArg (fun ω => x⁻¹ • ω) hh
      rw [show x⁻¹ • (x • Work.DoubleTransitivity.pt H) = Work.DoubleTransitivity.pt H from by
            rw [← mul_smul, inv_mul_cancel, one_smul],
          show x⁻¹ • (x ^ 2 • Work.DoubleTransitivity.pt H) = x • Work.DoubleTransitivity.pt H from by
            rw [← mul_smul, show x⁻¹ * x ^ 2 = x from by group]] at h2
      exact h2.symm
  -- `orderOf x` odd and `x ^ 2 ∈ H` force `x ∈ H`
  have hxH : x ∈ H := by
    obtain ⟨k, hk⟩ := hxodd
    have h2 : (x ^ 2) ^ (k + 1) = x := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf x + 1 from by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [← h2]
    exact Subgroup.pow_mem _ hx2H (k + 1)
  exact hxnotH hxH

end Work.NormalComplement.Sec5Fix.NF
