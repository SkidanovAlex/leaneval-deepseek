import Mathlib
import Submission.Work.AppXIShadow.Basic
import Submission.Work.AppXIShadow.AppII7
import Submission.Work.AppXIShadow.FixPSet
import Submission.Work.ThmF.ChV12.structureIdentity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIShadow

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

open Work.ThmF.ChV3

/-- **`st` lies in the normal subgroup `R`.**  In the standing context `CtxF H Q t s r P`, for the
normal subgroup `R ⊴ C_G(P)` of `Work.AppXIShadow.app3_regular_normal` (with `R ⊓ C_H(P) = Ker`,
`Ker ≤ R`, `[R,R] ≤ Ker`, `R` transitive on `fixP H P`), the element `st` lies in `R`.

This is the step that makes `(orderOf (s*t)).Prime` in App. XI Prop. 1 provable; it is *not*
formal from `R ⊴ C_G(P)`.

Route (all ingredients are in the repo).

1. **`r ∈ C_Q(P)`**, i.e. `r` centralises `P`.  For `x ∈ P`: `x` centralises `t` (`P ≤ centD H t`)
   and `s` (`s ∈ C_Q(P)`, `Work.AppXIShadow.s_mem_CQ`), and normalises `Q` (`Q ⊴ H ∋ x`), so
   conjugating the structure identity `t*s*t = r⁻¹ * t * r` (`c.sid`) by `x` gives
   `t * s * t = (x*r*x⁻¹)⁻¹ * t * (x*r*x⁻¹)`.  By the *uniqueness* of the pair `(s, r⁻¹)` in
   `Work.ThmF.ChV12.structureIdentity` (applied to `c.split.toData`), `x*r*x⁻¹ = r`.
2. Hence `u := r * t ∈ C_G(P)` and `t = u * s * u⁻¹` (`u s u⁻¹ = (rt)s(rt)⁻¹ = t`).
3. In the quotient `L̄ = C_G(P) ⧸ KerIn H Q P t` (`KerIn` is normal in `C_G(P)`: it is the kernel
   of the action, `Work.AppXIShadow.fixP_kernel_iff`), one has `L̄ = A ⋊ M̄` with
   `A := R ⧸ KerIn.subgroupOf R`, `M̄ := fixPStab c ⧸ KerIn`: `A ⊓ M̄ = 1` is `hstab`, and
   `A · M̄ = L̄` follows from `L = R · M` (`M = fixPStab c = Stab(∞)`), i.e. from transitivity of
   `R` (`htr`).
4. Write `ū = ā * m̄` with `ā ∈ A`, `m̄ ∈ M̄`; then `t̄ = ū s̄ ū⁻¹ = (ā w ā⁻¹ w⁻¹) * w` with
   `w := m̄ s̄ m̄⁻¹`, and since `A` is abelian (`hRK`) the `A`-component acts trivially on `A` by
   conjugation, so the conjugation action of `t̄` on `A` equals that of `w`.  But `s̄` acts on `A`
   as *inversion*: `s ∈ C_Q(P) ∖ {1}` acts fixed-point-freely on `A ∖ {1}` (`C_Q(P)` is sharply
   transitive there by `Work.AppXIShadow.CQ_regular_on_fixP`, and `xK ↦ x • ∞` interwines the
   conjugation action with the left action), and a fixed-point-free involution of the abelian
   group `A` is inversion; inversion is central in `Aut A` since `A` is abelian, so `w` acts as
   inversion as well.  Hence `t` acts on `A` as inversion.
5. Therefore `st` acts trivially on `A`, i.e. `st ∈ C_{L̄}(A)`.  As `L̄ = A ⋊ M̄` and `M̄` acts
   faithfully on `A` (an `m ∈ M` conjugating `R` into `R * Ker` fixes `fixP H P` pointwise, hence
   lies in `Ker` by `Work.AppXIShadow.fixP_kernel_iff`), `C_{L̄}(A) = A`, so `st ∈ R`. -/
theorem s_mul_t_mem_R {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (R : Subgroup ↥(Work.AppXIShadow.centP P)) (hRn : R.Normal)
    (hKle : Work.AppXIShadow.KerIn H Q P t ≤ R)
    (hRK : ⁅R, R⁆ ≤ Work.AppXIShadow.KerIn H Q P t)
    (hstab : R ⊓ Work.AppXIShadow.fixPStab c = Work.AppXIShadow.KerIn H Q P t)
    (htr : ∀ ω : ↥(Work.AppXIShadow.fixP H P),
      ∃ x ∈ R, x • Work.AppXIShadow.fixPBaseC c = ω) :
    Work.AppXIShadow.sMulT c ∈ R := by
  classical
  -- ## Step 1: `r` centralises `P`
  have hrC : r ∈ centP P := by
    have hsplit := c.split
    have ht2 : t * t = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [hsplit.invol, pow_two] at h
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    obtain ⟨p, _hp, huniq⟩ :=
      Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hsplit)
    have hsr' : t * s * t⁻¹ = r⁻¹ * t * (r⁻¹)⁻¹ := by rw [htinv, inv_inv]; exact c.sid
    have hsol : (s, r⁻¹) = p := huniq (s, r⁻¹) ⟨c.s_mem, c.s_inv, Q.inv_mem c.r_mem, hsr'⟩
    have hp2 : r⁻¹ = p.2 := congrArg Prod.snd hsol
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hxH : x ∈ H := P_le_H c hx
    have hxt : x * t = t * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (P_le_centralizer_t c hx)
    have hxs : x * s = s * x :=
      Subgroup.mem_centralizer_iff.mp (s_mem_CQ c).2 x hx
    have hxrQ : x * r⁻¹ * x⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hsplit.normal hxH) r⁻¹).mp (Q.inv_mem c.r_mem)
    have hxt' : x * t * x⁻¹ = t := by rw [hxt]; group
    have hxs' : x * s * x⁻¹ = s := by rw [hxs]; group
    have h1 : x * (t * s * t) * x⁻¹ = t * s * t := by
      calc x * (t * s * t) * x⁻¹
          = (x * t * x⁻¹) * (x * s * x⁻¹) * (x * t * x⁻¹) := by group
        _ = t * s * t := by rw [hxt', hxs']
    have h2 : x * (r⁻¹ * t * r) * x⁻¹ = (x * r⁻¹ * x⁻¹) * t * (x * r * x⁻¹) := by
      calc x * (r⁻¹ * t * r) * x⁻¹
          = (x * r⁻¹ * x⁻¹) * (x * t * x⁻¹) * (x * r * x⁻¹) := by group
        _ = (x * r⁻¹ * x⁻¹) * t * (x * r * x⁻¹) := by rw [hxt']
    have hconj : t * s * t⁻¹ = (x * r⁻¹ * x⁻¹) * t * (x * r⁻¹ * x⁻¹)⁻¹ := by
      rw [htinv]
      calc t * s * t = x * (t * s * t) * x⁻¹ := h1.symm
        _ = x * (r⁻¹ * t * r) * x⁻¹ := by rw [c.sid]
        _ = (x * r⁻¹ * x⁻¹) * t * (x * r * x⁻¹) := h2
        _ = (x * r⁻¹ * x⁻¹) * t * (x * r⁻¹ * x⁻¹)⁻¹ := by group
    have hsol2 : (s, x * r⁻¹ * x⁻¹) = p :=
      huniq (s, x * r⁻¹ * x⁻¹) ⟨c.s_mem, c.s_inv, hxrQ, hconj⟩
    have hxrr : x * r⁻¹ * x⁻¹ = r⁻¹ := (congrArg Prod.snd hsol2).trans hp2.symm
    have hconv : x * r * x⁻¹ = r := by
      have h := congrArg Inv.inv hxrr
      rw [show (x * r⁻¹ * x⁻¹)⁻¹ = x * r * x⁻¹ from by group, inv_inv] at h
      exact h
    exact mul_inv_eq_iff_eq_mul.mp hconv
  -- ## elements of `C_G(P)`
  let sC : ↥(centP P) := ⟨s, s_mem_centP c⟩
  let tC : ↥(centP P) := ⟨t, t_mem_centP c⟩
  let rC : ↥(centP P) := ⟨r, hrC⟩
  let uC : ↥(centP P) := rC * tC
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [c.split.invol, pow_two] at h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hst_eq : sMulT c = sC * tC := by
    apply Subtype.ext
    rfl
  have ht_eq : tC = uC * sC * uC⁻¹ := by
    apply Subtype.ext
    show t = (r * t) * s * (r * t)⁻¹
    rw [mul_inv_rev]
    calc t = r * (r⁻¹ * t * r) * r⁻¹ := by group
      _ = r * (t * s * t) * r⁻¹ := by rw [← c.sid]
      _ = r * (t * s * t⁻¹) * r⁻¹ := by rw [htinv]
      _ = (r * t) * s * (t⁻¹ * r⁻¹) := by group
  -- ## `s` acts on `R/KerIn` as inversion
  have hsC_base : sC • fixPBaseC c = fixPBaseC c := by
    apply Subtype.ext
    rw [fixP_smul_coe, fixPBase_coe]
    show s • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [Work.ThreePoints.smul_mk, mul_one]
    exact QuotientGroup.eq.mpr (by simpa using H.inv_mem (CQ_le_H c (s_mem_CQ c)))
  have hKiff : ∀ z ∈ R, z ∈ KerIn H Q P t ↔ z • fixPBaseC c = fixPBaseC c := by
    intro z hz
    constructor
    · intro h
      exact MulAction.mem_stabilizer_iff.mp (KerIn_le_fixPStab c h)
    · intro h
      have hz2 : z ∈ R ⊓ fixPStab c := ⟨hz, MulAction.mem_stabilizer_iff.mpr h⟩
      rwa [hstab] at hz2
  have hs_fpf : ∀ ω : ↥(fixP H P), sC • ω = ω → ω = fixPBaseC c := by
    intro ω hω
    by_contra hne
    have hne' : (ω : G ⧸ H) ≠ ((1 : G) : G ⧸ H) := by
      intro hc
      exact hne (Subtype.ext (hc.trans (fixPBase_coe H P (P_le_H c)).symm))
    have hfix : s • (ω : G ⧸ H) = (ω : G ⧸ H) := by
      have h := congrArg Subtype.val hω
      rw [fixP_smul_coe] at h
      exact h
    exact s_ne_one c (CQ_free_on_fixP c (s_mem_CQ c) ω.2 hne' hfix)
  have hsC_sq : sC * sC = 1 := by
    apply Subtype.ext
    show s * s = 1
    have h := pow_orderOf_eq_one s
    rw [c.s_inv] at h
    simpa [pow_two] using h
  have hsC_inv : (sC)⁻¹ = sC := inv_eq_of_mul_eq_one_right hsC_sq
  have hs_inv : ∀ x ∈ R, sC * x * sC⁻¹ * x ∈ KerIn H Q P t := by
    intro x hx
    have hx'R : sC * x * sC⁻¹ ∈ R := hRn.conj_mem x hx sC
    set x' : ↥(centP P) := sC * x * sC⁻¹ with hx'def
    have hθ : sC * (x * x') * sC⁻¹ = x' * x := by
      rw [hx'def, hsC_inv]
      calc sC * (x * (sC * x * sC)) * sC
          = sC * x * sC * x * (sC * sC) := by group
        _ = sC * x * sC * x := by rw [hsC_sq, mul_one]
        _ = (sC * x * sC) * x := by group
    have hab : (x' * x) • fixPBaseC c = (x * x') • fixPBaseC c := by
      have hk : (x' * x)⁻¹ * (x * x') ∈ KerIn H Q P t := by
        have h := hRK (Subgroup.commutator_mem_commutator (R.inv_mem hx) (R.inv_mem hx'R))
        simpa [commutatorElement_def, mul_inv_rev, mul_assoc] using h
      have hkb : ((x' * x)⁻¹ * (x * x')) • fixPBaseC c = fixPBaseC c :=
        MulAction.mem_stabilizer_iff.mp (KerIn_le_fixPStab c hk)
      calc (x' * x) • fixPBaseC c
          = (x' * x) • (((x' * x)⁻¹ * (x * x')) • fixPBaseC c) := by rw [hkb]
        _ = ((x' * x) * ((x' * x)⁻¹ * (x * x'))) • fixPBaseC c := by rw [← mul_smul]
        _ = (x * x') • fixPBaseC c := by congr 1; group
    have hstep : (sC * (x * x') * sC⁻¹) • (sC • fixPBaseC c)
        = (sC * (x * x')) • fixPBaseC c := by
      rw [← mul_smul]
      congr 1
      group
    have hpt : sC • ((x * x') • fixPBaseC c) = (x * x') • fixPBaseC c := by
      calc sC • ((x * x') • fixPBaseC c)
          = (sC * (x * x')) • fixPBaseC c := by rw [← mul_smul]
        _ = (sC * (x * x') * sC⁻¹) • (sC • fixPBaseC c) := hstep.symm
        _ = (sC * (x * x') * sC⁻¹) • fixPBaseC c := by rw [hsC_base]
        _ = (x' * x) • fixPBaseC c := by rw [hθ]
        _ = (x * x') • fixPBaseC c := hab
    have hxx'K : x * x' ∈ KerIn H Q P t := by
      rw [hKiff (x * x') (R.mul_mem hx hx'R)]
      exact hs_fpf ((x * x') • fixPBaseC c) hpt
    have hx'xK : x' * x ∈ KerIn H Q P t := by
      rw [hKiff (x' * x) (R.mul_mem hx'R hx)]
      rw [hab]
      exact MulAction.mem_stabilizer_iff.mp (KerIn_le_fixPStab c hxx'K)
    exact hx'xK
  -- ## `t` acts on `R/KerIn` as inversion
  have ht_inv : ∀ x ∈ R, tC * x * tC⁻¹ * x ∈ KerIn H Q P t := by
    intro x hx
    set y : ↥(centP P) := uC⁻¹ * x * uC with hydef
    have hyR : y ∈ R := by
      have h := hRn.conj_mem x hx (uC⁻¹)
      simpa [hydef, inv_inv] using h
    obtain ⟨kt, hktK, hkt⟩ : ∃ kt ∈ KerIn H Q P t, sC * y * sC⁻¹ = kt * y⁻¹ :=
      ⟨sC * y * sC⁻¹ * y, hs_inv y hyR, by group⟩
    have hconj : tC * x * tC⁻¹ = (uC * kt * uC⁻¹) * x⁻¹ := by
      have h1 : tC * x * tC⁻¹ = uC * (sC * y * sC⁻¹) * uC⁻¹ := by
        rw [ht_eq, hydef]; group
      rw [h1, hkt]
      have hyx : uC * y * uC⁻¹ = x := by rw [hydef]; group
      have hyix : uC * y⁻¹ * uC⁻¹ = x⁻¹ := by rw [← hyx]; group
      rw [← hyix]
      group
    have hmain : tC * x * tC⁻¹ * x = uC * kt * uC⁻¹ := by
      rw [hconj]
      group
    rw [hmain]
    exact (KerIn_normal c).conj_mem kt hktK uC
  -- ## `st` acts trivially on `R/KerIn`
  have hst_inv : ∀ x ∈ R, (sC * tC) * x * (sC * tC)⁻¹ * x⁻¹ ∈ KerIn H Q P t := by
    intro x hx
    obtain ⟨kt, hktK, hkt⟩ : ∃ kt ∈ KerIn H Q P t, tC * x * tC⁻¹ = kt * x⁻¹ :=
      ⟨tC * x * tC⁻¹ * x, ht_inv x hx, by group⟩
    obtain ⟨ks, hksK, hks⟩ : ∃ ks ∈ KerIn H Q P t, sC * x⁻¹ * sC⁻¹ = ks * x :=
      ⟨sC * x⁻¹ * sC⁻¹ * x⁻¹, hs_inv x⁻¹ (R.inv_mem hx), by group⟩
    have hmain : (sC * tC) * x * (sC * tC)⁻¹ * x⁻¹ = (sC * kt * sC⁻¹) * ks := by
      calc (sC * tC) * x * (sC * tC)⁻¹ * x⁻¹
          = sC * (tC * x * tC⁻¹) * sC⁻¹ * x⁻¹ := by group
        _ = sC * (kt * x⁻¹) * sC⁻¹ * x⁻¹ := by rw [hkt]
        _ = (sC * kt * sC⁻¹) * (sC * x⁻¹ * sC⁻¹) * x⁻¹ := by group
        _ = (sC * kt * sC⁻¹) * (ks * x) * x⁻¹ := by rw [hks]
        _ = (sC * kt * sC⁻¹) * ks := by group
    rw [hmain]
    exact Subgroup.mul_mem _ ((KerIn_normal c).conj_mem kt hktK sC) hksK
  -- ## the faithfulness step
  have memK : ∀ (m : ↥(centP P)), m ∈ fixPStab c →
      (∀ x ∈ R, m * x * m⁻¹ * x⁻¹ ∈ KerIn H Q P t) → m ∈ KerIn H Q P t := by
    intro m hm hcen
    rw [mem_KerIn_iff c]
    intro ω
    obtain ⟨x, hxR, hxb⟩ := htr ω
    rw [← hxb]
    have hk : m * x * m⁻¹ * x⁻¹ ∈ KerIn H Q P t := hcen x hxR
    have hkm : ∀ ω' : ↥(fixP H P), (m * x * m⁻¹ * x⁻¹) • ω' = ω' := (mem_KerIn_iff c).mp hk
    calc m • (x • fixPBaseC c)
        = (m * x) • fixPBaseC c := by rw [mul_smul]
      _ = ((m * x * m⁻¹ * x⁻¹) * x * m) • fixPBaseC c := by congr 1; group
      _ = (m * x * m⁻¹ * x⁻¹) • (x • (m • fixPBaseC c)) := by simp only [mul_smul]
      _ = (m * x * m⁻¹ * x⁻¹) • (x • fixPBaseC c) := by
            rw [MulAction.mem_stabilizer_iff.mp hm]
      _ = x • fixPBaseC c := hkm _
  -- ## assembly
  obtain ⟨r0, hr0R, hr0base⟩ := htr (sMulT c • fixPBaseC c)
  set mC : ↥(centP P) := r0⁻¹ * sMulT c with hmdef
  have hmstab : mC ∈ fixPStab c := by
    rw [MulAction.mem_stabilizer_iff, hmdef]
    calc (r0⁻¹ * sMulT c) • fixPBaseC c
        = r0⁻¹ • (sMulT c • fixPBaseC c) := by rw [mul_smul]
      _ = r0⁻¹ • (r0 • fixPBaseC c) := by rw [hr0base]
      _ = fixPBaseC c := by rw [inv_smul_smul]
  have hmcen : ∀ x ∈ R, mC * x * mC⁻¹ * x⁻¹ ∈ KerIn H Q P t := by
    intro x hx
    obtain ⟨k1, hk1K, hk1⟩ :
        ∃ k1 ∈ KerIn H Q P t, (sC * tC) * x * (sC * tC)⁻¹ = k1 * x :=
      ⟨(sC * tC) * x * (sC * tC)⁻¹ * x⁻¹, hst_inv x hx, by group⟩
    have hcomm : (r0⁻¹ * x * r0) * x⁻¹ ∈ KerIn H Q P t := by
      have h := hRK (Subgroup.commutator_mem_commutator (R.inv_mem hr0R) hx)
      simpa [commutatorElement_def, mul_assoc] using h
    have hmv : mC = r0⁻¹ * (sC * tC) := by rw [hmdef, hst_eq]
    have hmain : mC * x * mC⁻¹ * x⁻¹
        = (r0⁻¹ * k1 * r0) * ((r0⁻¹ * x * r0) * x⁻¹) := by
      calc mC * x * mC⁻¹ * x⁻¹
          = r0⁻¹ * ((sC * tC) * x * (sC * tC)⁻¹) * r0 * x⁻¹ := by rw [hmv]; group
        _ = r0⁻¹ * (k1 * x) * r0 * x⁻¹ := by rw [hk1]
        _ = (r0⁻¹ * k1 * r0) * ((r0⁻¹ * x * r0) * x⁻¹) := by group
    rw [hmain]
    have hk1c : r0⁻¹ * k1 * r0 ∈ KerIn H Q P t := by
      simpa using (KerIn_normal c).conj_mem k1 hk1K (r0⁻¹)
    exact Subgroup.mul_mem _ hk1c hcomm
  have hmK : mC ∈ KerIn H Q P t := memK mC hmstab hmcen
  have hfinal : sMulT c = r0 * mC := by
    rw [hmdef]
    group
  rw [hfinal]
  exact R.mul_mem hr0R (hKle hmK)

end Work.AppXIShadow
