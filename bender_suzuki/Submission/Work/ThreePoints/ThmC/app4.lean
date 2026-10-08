import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.app4_blackburn
import Submission.Work.ThreePoints.ThmC.app4_lift
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Internal
import Submission.Work.Coprime.abelian_split
import Submission.Work.Coprime.commutator_commutator_eq
import Submission.Work.Coprime.fixedPoints_ne_bot_of_isPGroup
import Submission.Work.Coprime.fixedPoints_quotient
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.Basic
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.centralizer_pPrimePCore_le
import Submission.Work.Fitting.piCore_quotient_eq_bot
import Submission.Work.Fitting.isPSolvable_of_solvable
import Submission.Work.Fitting.isPSolvable_quotient
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.GlaubermanZJ.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped commutatorElement Pointwise

namespace Work.ThreePoints.ThmC

/-- **Peterfalvi I Appendix IV (p. 208): the result of Thompson and Bender.**  Let `p` be an odd
prime, `M` a finite **solvable** group and `P` a `p`-subgroup of `M` such that every element of order
`p` of `C_M(P)` lies in `P` (in particular this holds when `P` is a `p`-Sylow of `P·C_M(P)`, which is
the form used in Ch. II §3).  Then every `p'`-subgroup `X` of `M` normalised by `P` is contained in
`O_{p'}(M) = pPrimeCore p M`.

(The source states this for `p`-constrained `M`; solvable groups are `p`-constrained, and only the
solvable case is applied.  Route: Huppert VI.6.5 for `p`-constraint, then Appendix IV's fourth
numbered item (Blackburn, via the third one, Baer's result on odd-order groups with abelian central
quotient) and its first item (Huppert III.13.3/13.4).  Appendix IV pp. 208–210 is transcribed in
`REFS/peterfalvi_I_app1_4.md`.) -/
theorem app4 {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hsolv : Group.IsSolvable M) {P X : Subgroup M} (hP : IsPGroup p P)
    (hC : ∀ x : M, x ∈ Subgroup.centralizer (P : Set M) → orderOf x = p → x ∈ P)
    (hXp : Nat.Coprime (Nat.card X) p) (hPX : P ≤ Subgroup.normalizer (X : Set M)) :
    X ≤ Submission.Blueprint.pPrimeCore p M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
  -- the `p'`-core
  set N : Subgroup M := Work.Fitting.pPrimeCore p M with hNdef
  haveI hNn : N.Normal := inferInstance
  have hNcop : Nat.Coprime (Nat.card ↥N) p :=
    (Work.GlaubermanZJ.isPiNat_ne_iff_coprime hp).mp
      (Work.Fitting.piCore_isPiNat M (fun q => q ≠ p))
  -- the quotient by the `p'`-core
  set q : M →* M ⧸ N := QuotientGroup.mk' N with hqdef
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  haveI : Finite (M ⧸ N) := Finite.of_surjective q hqsurj
  haveI hpsolv : Work.Fitting.IsPSolvable p M := Work.Fitting.isPSolvable_of_solvable p M
  haveI hpsolvQ : Work.Fitting.IsPSolvable p (M ⧸ N) := Work.Fitting.isPSolvable_quotient p M N
  -- the Fitting subgroup of the quotient, and the images of `X` and `P`
  set Q : Subgroup (M ⧸ N) := Work.Fitting.pCore p (M ⧸ N) with hQdef
  have hQpg : IsPGroup p Q := Work.Fitting.isPGroup_pCore (G := M ⧸ N) hp
  haveI hQn : Q.Normal := inferInstance
  set Xb : Subgroup (M ⧸ N) := X.map q with hXbdef
  set Pb : Subgroup (M ⧸ N) := P.map q with hPbdef
  have hXb_cop : Nat.Coprime (Nat.card ↥Xb) p :=
    hXp.coprime_dvd_left (Subgroup.card_map_dvd X q)
  have hPb_pg : IsPGroup p Pb := hP.map q
  have hXbQ : Xb ≤ Subgroup.normalizer (Q : Set (M ⧸ N)) := by
    rw [Subgroup.le_normalizer_iff]
    intro x _ y hy
    exact hQn.conj_mem y hy x
  have hPbQ : Pb ≤ Subgroup.normalizer (Q : Set (M ⧸ N)) := by
    rw [Subgroup.le_normalizer_iff]
    intro x _ y hy
    exact hQn.conj_mem y hy x
  have hPbX : Pb ≤ Subgroup.normalizer (Xb : Set (M ⧸ N)) := by
    rw [Subgroup.le_normalizer_iff]
    rintro - ⟨g, hg, rfl⟩ - ⟨y₀, hy₀, rfl⟩
    exact ⟨g * y₀ * g⁻¹, Subgroup.le_normalizer_iff.mp hPX g hg y₀ hy₀, by
      rw [map_mul, map_mul, map_inv]⟩
  -- the elements of order `p` of `C_Q(P)` are centralised by `X`
  have hXbQbot : Xb ⊓ Q = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQpg
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_right k hXb_cop
  have hcent : ⁅Xb, Work.PGroup.omega1 (M ⧸ N) p
      (Q ⊓ Subgroup.centralizer (Pb : Set (M ⧸ N)))⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine (Subgroup.closure_le _).mpr ?_
    rintro a ⟨ha, hap⟩
    change a ∈ Subgroup.centralizer (Xb : Set (M ⧸ N))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have haQ : a ∈ Q := (Subgroup.mem_inf.mp ha).1
    have haP : a ∈ Subgroup.centralizer (Pb : Set (M ⧸ N)) := (Subgroup.mem_inf.mp ha).2
    rcases eq_or_ne a 1 with rfl | ha1
    · rw [commutatorElement_one_right]
    · -- lift `a` to an element of order `p` in `C_M(P)`
      have haord : orderOf a = p := by
        have hdvd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hap
        rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
        · exact absurd (orderOf_eq_one_iff.mp h1) ha1
        · exact hp'
      obtain ⟨y, hy⟩ : ∃ y : M, q y = a := hqsurj a
      have hyP : ∀ g ∈ P, q (g * y * g⁻¹) = q y := by
        intro g hg
        have hmem : q g ∈ Pb := ⟨g, hg, rfl⟩
        have hcomm := (Subgroup.mem_centralizer_iff.mp haP) (q g) hmem
        simp only [map_mul, map_inv, hy, hcomm]
        exact mul_inv_cancel_right _ _
      obtain ⟨a₀, ha₀C, ha₀ord, ha₀im⟩ :=
        app4_lift hp N hNcop hP (P := P) hyP (by rw [hy]; exact haord)
      have ha₀P : a₀ ∈ P := hC a₀ ha₀C ha₀ord
      have haPbar : a ∈ Pb := ⟨a₀, ha₀P, by rw [ha₀im, hy]⟩
      have hxX : x ∈ Xb := hx
      -- `⁅x,a⁆` lies in both `Xb` and `Q`, hence is trivial
      have hmemX : ⁅x, a⁆ ∈ Xb := by
        have h1 : a * x⁻¹ * a⁻¹ ∈ Xb :=
          (Subgroup.mem_normalizer_iff.mp (hPbX haPbar) x⁻¹).mp (Xb.inv_mem hxX)
        have h2 : x * (a * x⁻¹ * a⁻¹) = ⁅x, a⁆ := by
          simp only [commutatorElement_def, mul_assoc]
        rw [← h2]
        exact Xb.mul_mem hxX h1
      have hmemQ : ⁅x, a⁆ ∈ Q := by
        have h1 : x * a * x⁻¹ ∈ Q := hQn.conj_mem a haQ x
        have h2 : (x * a * x⁻¹) * a⁻¹ = ⁅x, a⁆ := by
          simp only [commutatorElement_def, mul_assoc]
        rw [← h2]
        exact Q.mul_mem h1 (Q.inv_mem haQ)
      have hbot : ⁅x, a⁆ ∈ (⊥ : Subgroup (M ⧸ N)) := by
        rw [← hXbQbot]
        exact Subgroup.mem_inf.mpr ⟨hmemX, hmemQ⟩
      rw [Subgroup.mem_bot] at hbot
      exact hbot
  -- Blackburn's theorem
  have hcomm_bot : ⁅Xb, Q⁆ = ⊥ := app4_blackburn hp hpodd hQpg hXb_cop hPb_pg hXbQ hPbQ hPbX hcent
  have hXb_cent : Xb ≤ Subgroup.centralizer (Q : Set (M ⧸ N)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
  -- `p`-constraint
  have hcore : Work.Fitting.pPrimeCore p (M ⧸ N) = ⊥ :=
    Work.Fitting.piCore_quotient_eq_bot (fun r => r ≠ p) M
  have hXbQ_le : Xb ≤ Q :=
    hXb_cent.trans (Work.Fitting.centralizer_pCore_le_of_pPrimeCore_eq_bot p (M ⧸ N) hp hcore)
  -- `Xb` is both a `p`-group and a `p'`-group, hence trivial
  have hXb_bot : Xb = ⊥ := by
    have h1 : Xb ⊓ Q = Xb := inf_eq_left.mpr hXbQ_le
    rw [← h1, hXbQbot]
  -- conclude
  have hX_N : X ≤ N := by
    have hmap : X.map q = ⊥ := by rw [← hXbdef]; exact hXb_bot
    have h1 := (Subgroup.map_eq_bot_iff X (f := q)).mp hmap
    rwa [hqdef, QuotientGroup.ker_mk'] at h1
  exact hX_N

end Work.ThreePoints.ThmC
