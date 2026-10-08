import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.H8.frob_irred_le_Mk
import Submission.Work.Higman.H8.frob_submodule_bijective
import Submission.Work.Higman.HS.omega1_singer_iso
import Submission.Work.Higman.H8.c4_card_le
import Submission.Work.Higman.H8.layer_of_end_injection
import Submission.Work.Higman.HS.two_cover_pairing
import Submission.Work.Higman.H8.c4nocard_nu_iso_xi
import Submission.Work.Higman.SZ.model
import Submission.Work.Higman.exists_singer_iso
import Submission.Work.Higman.MSA.l8_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Higman.HS

open scoped commutatorElement

/-! ## The Singer/field model of `Ω₁(P)` in `GaloisField` coordinates

This is the `GaloisField 2 n` form of `Work.Higman.HS.omega1_singer_iso`, obtained by the same
route: the `𝔽₂⟨ξ⟩`-module `Ω₁(P)` is identified through `Work.Higman.exists_singer_iso` with
`GF(2 ^ n)` in such a way that `ξ` becomes multiplication by a primitive element `ν`. -/
theorem two_cover_singer_data {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P) :
    ∃ (n : ℕ) (ν : (GaloisField 2 n)ˣ) (ζ : GaloisField 2 n ≃ ↥(Work.Higman.omega1 P)),
      2 ≤ n ∧ orderOf ν = 2 ^ n - 1 ∧
      (∀ x y : GaloisField 2 n, ζ (x + y) = ζ x * ζ y) ∧
      (∀ x : GaloisField 2 n, ζ ((ν : GaloisField 2 n) * x) = Work.Higman.xiZ h (ζ x)) := by
  classical
  let V := Additive ↥(Work.Higman.omega1 P)
  letI : CommGroup ↥(Work.Higman.omega1 P) :=
    Work.Higman.SZ.commGroup_subtype_of_abelian (fun x hx y hy => h.omega1_comm hx hy)
  have hsq : ∀ z : ↥(Work.Higman.omega1 P), z * z = 1 := fun z => Subtype.ext (by
    show (z : P) * (z : P) = 1
    rw [← pow_two]; exact h.mem_omega1.mp z.2)
  letI : Module (ZMod 2) V := Work.Higman.SZ.module_zmod2_of_sq_one hsq
  let ξZ : ↥(Work.Higman.omega1 P) ≃* ↥(Work.Higman.omega1 P) := Work.Higman.xiZ h
  let ξVadd : V ≃+ V := ξZ.toAdditive
  let σlin : V →ₗ[ZMod 2] V := AddMonoidHom.toZModLinearMap 2 (ξVadd : V →+ V)
  have hσlin_apply : ∀ v : V, σlin v = ξVadd v := fun v => rfl
  have hσlin : Function.Bijective σlin :=
    ⟨fun a b hab => ξVadd.injective (by rw [← hσlin_apply, ← hσlin_apply]; exact hab),
      fun b => ⟨ξVadd.symm b, by rw [hσlin_apply]; exact ξVadd.apply_symm_apply b⟩⟩
  let ξV : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective σlin hσlin
  have hξV_apply : ∀ v : V, ξV v = Additive.ofMul (ξZ (Additive.toMul v)) := by
    intro v; show σlin v = _; rw [hσlin_apply]; rfl
  have hξV_pow : ∀ (k : ℕ) (v : V),
      (ξV ^ k) v = Additive.ofMul ((ξZ ^ k) (Additive.toMul v)) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [pow_succ', LinearEquiv.mul_apply, ih, hξV_apply, toMul_ofMul]
        congr 1
        rw [pow_succ']
        rfl
  have hord_z : ∀ z : ↥(Work.Higman.omega1 P), z ≠ 1 → orderOf ((z : P)) = 2 := by
    intro z hz
    have hz2 : (z : P) ^ 2 = 1 := h.mem_omega1.mp z.2
    have hd : orderOf ((z : P)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h1)) hz
    · exact h1
  have htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξV ^ k) a = b := by
    intro a b ha hb
    have ha' : Additive.toMul a ≠ 1 := by
      intro h1; exact ha (by rw [← ofMul_toMul a, h1]; rfl)
    have hb' : Additive.toMul b ≠ 1 := by
      intro h1; exact hb (by rw [← ofMul_toMul b, h1]; rfl)
    obtain ⟨k, hk⟩ := h.trans ((Additive.toMul a : ↥(Work.Higman.omega1 P)) : P)
      ((Additive.toMul b : ↥(Work.Higman.omega1 P)) : P)
      (hord_z (Additive.toMul a) ha') (hord_z (Additive.toMul b) hb')
    refine ⟨k, ?_⟩
    rw [hξV_pow, ← ofMul_toMul b]
    congr 1
    refine Subtype.ext ?_
    rw [Work.Higman.xiZ_pow_coe h k (Additive.toMul a)]
    exact hk
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have hVcard : Nat.card V = 2 ^ n := hn
  have hn2 : 2 ≤ n := by
    by_contra hcon
    push Not at hcon
    have h1 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega : n ≤ 1)
    have h4 : 4 ≤ 2 ^ n := by rw [← hn]; exact h.omega1_card_ge_four
    norm_num at h1
    omega
  obtain ⟨hVord, hVfree⟩ := Work.Higman.singer_data_of_transitive hn2 hVcard ξV htrans
  obtain ⟨φ, lam, hlamord, hφ⟩ :=
    Work.Higman.exists_singer_iso (n := n) (V := V) (by omega) hVcard ξV hVord hVfree
  refine ⟨n, lam, φ.symm.toEquiv.trans Additive.toMul, hn2, hlamord, ?_, ?_⟩
  · intro x y
    show Additive.toMul (φ.symm (x + y)) = Additive.toMul (φ.symm x) * Additive.toMul (φ.symm y)
    rw [map_add, toMul_add]
  · intro x
    have h1 : ξV (φ.symm x) = φ.symm (((lam : (GaloisField 2 n)ˣ) : GaloisField 2 n) * x) := by
      apply φ.injective
      rw [hφ (φ.symm x), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    show Additive.toMul (φ.symm (((lam : (GaloisField 2 n)ˣ) : GaloisField 2 n) * x))
      = ξZ (Additive.toMul (φ.symm x))
    rw [← h1, hξV_apply, toMul_ofMul]

/-! ## The two-cover layer twist -/

theorem two_cover_layer_twist {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    {A D : Subgroup P} [hAn : A.Normal]
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hADne : A ≠ D)
    (hirrD : ∀ F' : Subgroup P, F'.Normal → F'.map (h.xi : MulAut P).toMonoidHom = F' →
      A ≤ F' → F' ≤ D → F' = A ∨ F' = D)
    (hDd : Bracket.bracket D D = Work.Higman.powSub A 2)
    (hDcard : Nat.card ↥D = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (_ : CharP F 2)
      (ν : F) (k : ℕ) (φ : P → F),
      Fintype.card F = 2 ^ n ∧ 2 ≤ n ∧ orderOf ν = 2 ^ n - 1 ∧ k < n ∧
      (∀ c c' : P, c ∈ D → c' ∈ D → φ (c * c') = φ c + φ c') ∧
      (∀ c : P, c ∈ D → (φ c = 0 ↔ c ∈ A)) ∧
      (∀ c : P, c ∈ D → φ (h.xi c) = ν ^ (1 - (2 : ℤ) ^ k) * φ c) ∧
      (∀ x : F, ∃ c : P, c ∈ D ∧ φ c = x) := by
  classical
  haveI hpowN : (Work.Higman.powSub A 2).Normal := Work.Higman.powSub_normal hAn 2
  -- ## The Singer data
  obtain ⟨n, νU, ζ, hn2, hνord, hζadd, hζmul⟩ := two_cover_singer_data h
  -- ## The commutator pairing `A/A² × D/A → Ω₁`
  obtain ⟨β, hβdef, hβadd1, hβadd2, hβnondeg⟩ := two_cover_pairing h hA hGs htop hAD hDd hcent
  -- ## The squaring isomorphism `A/A² ≅ Ω₁`
  obtain ⟨Φ, hΦbij, hΦxi⟩ := Work.Higman.H8.c4nocard_nu_iso_xi h hA htop hcard
  let νq : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) ≃* ↥(Work.Higman.omega1 P) :=
    MulEquiv.ofBijective Φ hΦbij
  have hνq_apply : ∀ q, νq q = Φ q := fun q => rfl
  have hxiZeq : Work.Higman.MSA.xiSubAut h (Work.Higman.map_xi_omega1 h) = Work.Higman.xiZ h :=
    MulEquiv.ext (fun z => Subtype.ext rfl)
  -- ## The `ξ`-action on `D/A`
  let ξD : (↥D ⧸ (A.subgroupOf D)) ≃* (↥D ⧸ (A.subgroupOf D)) :=
    QuotientGroup.congr (A.subgroupOf D) (A.subgroupOf D) (Work.Higman.MSA.xiSubAut h hDinv)
      (Work.Higman.MSA.map_xi_subgroupOf h hA.map_eq hDinv)
  have hξD_mk : ∀ d : ↥D,
      ξD (QuotientGroup.mk d) = QuotientGroup.mk (Work.Higman.MSA.xiSubAut h hDinv d) :=
    fun d => QuotientGroup.congr_mk _ _ _ _ d
  -- ## The `ξ`-action on `A/A²`
  have hA2inv : (Work.Higman.powSub A 2).map (h.xi : MulAut P).toMonoidHom
      = Work.Higman.powSub A 2 :=
    Work.Higman.map_powSub (h.xi : MulAut P) hA.map_eq 2
  have hξA2 : Subgroup.map (Work.Higman.MSA.xiSubAut h hA.map_eq)
      ((Work.Higman.powSub A 2).subgroupOf A) = (Work.Higman.powSub A 2).subgroupOf A :=
    Work.Higman.MSA.map_xi_subgroupOf h hA2inv hA.map_eq
  let ξA : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) ≃*
      (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) :=
    QuotientGroup.congr ((Work.Higman.powSub A 2).subgroupOf A)
      ((Work.Higman.powSub A 2).subgroupOf A) (Work.Higman.MSA.xiSubAut h hA.map_eq) hξA2
  have hξA_mk : ∀ a : ↥A,
      ξA (QuotientGroup.mk a) = QuotientGroup.mk (Work.Higman.MSA.xiSubAut h hA.map_eq a) :=
    fun a => QuotientGroup.congr_mk _ _ _ _ a
  have hνqxi : ∀ q : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A),
      νq (ξA q) = Work.Higman.xiZ h (νq q) := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hξA_mk a, hνq_apply, hνq_apply, hΦxi a, hxiZeq]
  -- ## `ξ`-equivariance of the pairing
  have hβxi : ∀ (w : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A))
      (v : (↥D ⧸ (A.subgroupOf D))),
      β (ξA w) (ξD v) = Work.Higman.xiZ h (β w v) := by
    intro w v
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective v
    apply Subtype.ext
    rw [hξA_mk a, hξD_mk d,
      hβdef (Work.Higman.MSA.xiSubAut h hA.map_eq a) (Work.Higman.MSA.xiSubAut h hDinv d),
      Work.Higman.xiZ_apply, hβdef a d, Work.Higman.MSA.xiSubAut_apply h hA.map_eq a,
      Work.Higman.MSA.xiSubAut_apply h hDinv d]
    exact (map_commutatorElement (h.xi : MulAut P) (a : P) (d : P)).symm
  -- ## Elementaries on `ζ`, `νq` and `β`
  have hζ0 : ζ (0 : GaloisField 2 n) = 1 := by
    have h1 := hζadd 0 0
    rw [add_zero] at h1
    have h2 := congrArg (fun t => (ζ 0)⁻¹ * t) h1
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h2
    exact h2.symm
  have hζsymm_mul : ∀ a b : ↥(Work.Higman.omega1 P),
      ζ.symm (a * b) = ζ.symm a + ζ.symm b := by
    intro a b
    apply ζ.injective
    rw [Equiv.apply_symm_apply, hζadd, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hζsymm_one : ζ.symm (1 : ↥(Work.Higman.omega1 P)) = 0 := by
    rw [← hζ0, Equiv.symm_apply_apply]
  have hζsymm_xi : ∀ y : ↥(Work.Higman.omega1 P),
      ζ.symm (Work.Higman.xiZ h y) = (νU : GaloisField 2 n) * ζ.symm y := by
    intro y
    apply ζ.injective
    rw [Equiv.apply_symm_apply, hζmul, Equiv.apply_symm_apply]
  have hβone1 : ∀ v : (↥D ⧸ (A.subgroupOf D)),
      β (1 : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A)) v = 1 := by
    intro v
    have h1 := hβadd1 (1 : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A))
      (1 : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A)) v
    rw [one_mul] at h1
    have h2 := congrArg (fun t => (β 1 v)⁻¹ * t) h1
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h2
    exact h2.symm
  have hβone2 : ∀ (q : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A)),
      β q (1 : (↥D ⧸ (A.subgroupOf D))) = 1 := by
    intro q
    have h1 := hβadd2 q (1 : (↥D ⧸ (A.subgroupOf D))) (1 : (↥D ⧸ (A.subgroupOf D)))
    rw [one_mul] at h1
    have h2 := congrArg (fun t => (β q 1)⁻¹ * t) h1
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h2
    exact h2.symm
  -- ## The function `Ψ` on representatives
  let PsiFun : (↥D ⧸ (A.subgroupOf D)) → GaloisField 2 n → GaloisField 2 n :=
    fun v x => ζ.symm (β (νq.symm (ζ x)) v)
  have hPsi0 : ∀ v, PsiFun v 0 = 0 := by
    intro v
    show ζ.symm (β (νq.symm (ζ 0)) v) = 0
    rw [hζ0, map_one, hβone1, hζsymm_one]
  have hPsiadd : ∀ v x y, PsiFun v (x + y) = PsiFun v x + PsiFun v y := by
    intro v x y
    show ζ.symm (β (νq.symm (ζ (x + y))) v) = ζ.symm (β (νq.symm (ζ x)) v)
      + ζ.symm (β (νq.symm (ζ y)) v)
    rw [hζadd x y, map_mul, hβadd1, hζsymm_mul]
  have hPsimul : ∀ v w x, PsiFun (v * w) x = PsiFun v x + PsiFun w x := by
    intro v w x
    show ζ.symm (β (νq.symm (ζ x)) (v * w)) = ζ.symm (β (νq.symm (ζ x)) v)
      + ζ.symm (β (νq.symm (ζ x)) w)
    rw [hβadd2, hζsymm_mul]
  have hPsi_one : ∀ x, PsiFun 1 x = 0 := by
    intro x
    show ζ.symm (β (νq.symm (ζ x)) 1) = 0
    rw [hβone2, hζsymm_one]
  have hPsiinj : ∀ v : (↥D ⧸ (A.subgroupOf D)), (∀ x, PsiFun v x = 0) → v = 1 := by
    intro v hv
    refine hβnondeg v ?_
    intro q
    obtain ⟨x, hx⟩ := ζ.surjective (νq q)
    have h2 : ζ.symm (β q v) = 0 := by
      have h3 : ζ.symm (β (νq.symm (ζ x)) v) = 0 := hv x
      rwa [show νq.symm (ζ x) = q from by rw [hx]; exact νq.symm_apply_apply q] at h3
    have h4 : β q v = 1 := by
      have h5 := congrArg ζ h2
      rwa [Equiv.apply_symm_apply, hζ0] at h5
    exact h4
  have hPsixi : ∀ v x, PsiFun (ξD v) x
      = (νU : GaloisField 2 n) * PsiFun v ((νU : GaloisField 2 n)⁻¹ * x) := by
    intro v x
    have h1 : νq.symm (ζ x) = ξA (νq.symm (ζ ((νU : GaloisField 2 n)⁻¹ * x))) := by
      apply νq.injective
      rw [MulEquiv.apply_symm_apply, hνqxi, MulEquiv.apply_symm_apply, ← hζmul,
        mul_inv_cancel_left₀ (Units.ne_zero νU)]
    show ζ.symm (β (νq.symm (ζ x)) (ξD v))
      = (νU : GaloisField 2 n) * ζ.symm (β (νq.symm (ζ ((νU : GaloisField 2 n)⁻¹ * x))) v)
    rw [h1, hβxi, hζsymm_xi]
  -- ## The `𝔽₂`-module `V = D/A`
  let V := Additive (↥D ⧸ (A.subgroupOf D))
  have hcommD : ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ ≤ A.subgroupOf D := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    have hmem : ⁅(x : P), (y : P)⁆ ∈ ⁅D, D⁆ := Subgroup.commutator_mem_commutator x.2 y.2
    rw [hDd] at hmem
    have hcoe : ((⁅x, y⁆ : ↥D) : P) = ⁅(x : P), (y : P)⁆ := map_commutatorElement D.subtype x y
    rw [hcoe]
    exact Work.Higman.powSub_le (by norm_num : 0 < 2) hmem
  letI : CommGroup (↥D ⧸ (A.subgroupOf D)) :=
    Work.Higman.SZ.commGroup_quot_of_commutator_le (A.subgroupOf D) hcommD
  have hV2 : ∀ u : (↥D ⧸ (A.subgroupOf D)), u * u = 1 := by
    intro u
    induction u using QuotientGroup.induction_on with
    | _ d =>
        show (QuotientGroup.mk d) * (QuotientGroup.mk d) = 1
        rw [← QuotientGroup.mk_mul]
        exact (QuotientGroup.eq_one_iff (N := A.subgroupOf D) (d * d)).mpr
          (Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using hsq (d : P)))
  letI : Module (ZMod 2) V := Work.Higman.SZ.module_zmod2_of_sq_one hV2
  let σlin : V →ₗ[ZMod 2] V := AddMonoidHom.toZModLinearMap 2 (ξD.toAdditive : V →+ V)
  have hσlin_apply : ∀ q, σlin (Additive.ofMul q) = Additive.ofMul (ξD q) := fun q => rfl
  have hσlin_bij : Function.Bijective σlin :=
    ⟨fun a b hab => ξD.toAdditive.injective hab,
      fun b => ⟨ξD.toAdditive.symm b, ξD.toAdditive.apply_symm_apply b⟩⟩
  let ξV : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective σlin hσlin_bij
  have hξV_apply : ∀ q, ξV (Additive.ofMul q) = Additive.ofMul (ξD q) := fun q => hσlin_apply q
  -- ## Cardinality of `V`
  have hsubcard : Nat.card ↥(A.subgroupOf D) = Nat.card ↥A := by
    let f : ↥(A.subgroupOf D) → ↥A := fun x => ⟨((x : ↥D) : P), x.2⟩
    let g : ↥A → ↥(A.subgroupOf D) := fun a => ⟨⟨(a : P), hAD a.2⟩, a.2⟩
    exact Nat.card_congr { toFun := f, invFun := g, left_inv := fun x => rfl, right_inv := fun x => rfl }
  have hVcard : Nat.card V = 2 ^ n := by
    have hq : Nat.card ↥(Work.Higman.omega1 P) = 2 ^ n := by
      rw [← Nat.card_congr ζ, Work.Higman.H8.card_galois (by omega)]
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf D)
    rw [hsubcard] at hmul
    have hD : Nat.card ↥D = (2 ^ n) ^ 3 := by rw [← hq]; exact hDcard
    have hA' : Nat.card ↥A = (2 ^ n) ^ 2 := by rw [← hq]; exact hcard
    rw [hD, hA'] at hmul
    have hdiv : Nat.card (↥D ⧸ (A.subgroupOf D)) = 2 ^ n := by
      have hmul' : (2 ^ n) * (2 ^ n) ^ 2
          = Nat.card (↥D ⧸ (A.subgroupOf D)) * (2 ^ n) ^ 2 := by
        rw [← hmul]; ring
      exact (Nat.mul_right_cancel (by positivity) hmul').symm
    show Nat.card (Additive (↥D ⧸ (A.subgroupOf D))) = 2 ^ n
    rw [Nat.card_congr Additive.ofMul]
    exact hdiv
  -- ## Simplicity of `V`
  have hnormal_of_contains : ∀ F' : Subgroup P, A ≤ F' → F'.Normal := by
    intro F' hAF
    refine Subgroup.Normal.mk (fun n hn g => ?_)
    have hc : ⁅g, n⁆ ∈ A := by
      have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
      rwa [hGs] at h1
    have h2 : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact F'.mul_mem (hAF hc) hn
  have hsimple : ∀ W : Submodule (ZMod 2) V, (∀ v ∈ W, ξV v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let E : Subgroup (↥D ⧸ (A.subgroupOf D)) :=
      { carrier := {q | Additive.ofMul q ∈ W}
        one_mem' := by
          show Additive.ofMul (1 : ↥D ⧸ (A.subgroupOf D)) ∈ W
          rw [ofMul_one]; exact W.zero_mem
        mul_mem' := by
          intro a b ha hb
          show Additive.ofMul (a * b) ∈ W
          rw [ofMul_mul]; exact W.add_mem ha hb
        inv_mem' := by
          intro a ha
          show Additive.ofMul a⁻¹ ∈ W
          rw [ofMul_inv]; exact W.neg_mem ha }
    have hEmem : ∀ q : (↥D ⧸ (A.subgroupOf D)), q ∈ E ↔ Additive.ofMul q ∈ W := fun q => Iff.rfl
    let Esub : Subgroup ↥D := E.comap (QuotientGroup.mk' (A.subgroupOf D))
    have hEmem2 : ∀ u : ↥D, u ∈ Esub ↔
        (QuotientGroup.mk u : (↥D ⧸ (A.subgroupOf D))) ∈ E := by
      intro u
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]
    have hEξ : ∀ u : ↥D, (QuotientGroup.mk u : (↥D ⧸ (A.subgroupOf D))) ∈ E →
        (QuotientGroup.mk (Work.Higman.MSA.xiSubAut h hDinv u)
          : (↥D ⧸ (A.subgroupOf D))) ∈ E := by
      intro u hu
      rw [hEmem] at hu ⊢
      have h1 : ξV (Additive.ofMul (QuotientGroup.mk u)) ∈ W := hW _ hu
      have h2 : ξV (Additive.ofMul (QuotientGroup.mk u))
          = Additive.ofMul (QuotientGroup.mk (Work.Higman.MSA.xiSubAut h hDinv u)) := by
        rw [hξV_apply, hξD_mk]
      rwa [h2] at h1
    set Fp : Subgroup P := Esub.map D.subtype with hFp
    have hAFp : A ≤ Fp := by
      intro a ha
      rw [hFp]
      refine Subgroup.mem_map.mpr ⟨(⟨a, hAD ha⟩ : ↥D), ?_, rfl⟩
      rw [hEmem2, hEmem]
      have h1 : (QuotientGroup.mk (⟨a, hAD ha⟩ : ↥D) : (↥D ⧸ (A.subgroupOf D))) = 1 :=
        (QuotientGroup.eq_one_iff (N := A.subgroupOf D) (⟨a, hAD ha⟩ : ↥D)).mpr
          (Subgroup.mem_subgroupOf.mpr ha)
      rw [h1, ofMul_one]; exact W.zero_mem
    have hFpD : Fp ≤ D := by rw [hFp]; exact Subgroup.map_subtype_le Esub
    have hFpinv_le : Fp.map (h.xi : MulAut P).toMonoidHom ≤ Fp := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [hFp] at hy ⊢
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_map.mpr ⟨(Work.Higman.MSA.xiSubAut h hDinv u : ↥D), ?_, ?_⟩
      · rw [hEmem2]
        exact hEξ u ((hEmem2 u).mp hu)
      · exact (Work.Higman.MSA.xiSubAut_apply h hDinv u)
    have hFpinv : Fp.map (h.xi : MulAut P).toMonoidHom = Fp :=
      Subgroup.eq_of_le_of_card_ge hFpinv_le
        (le_of_eq (Subgroup.card_map_of_injective (h.xi : MulAut P).injective).symm)
    have hFpn : Fp.Normal := hnormal_of_contains Fp hAFp
    rcases hirrD Fp hFpn hFpinv hAFp hFpD with hFA | hFD
    · left
      rw [Submodule.eq_bot_iff]
      intro y hy
      obtain ⟨q, rfl⟩ : ∃ q, Additive.ofMul q = y := ⟨Additive.toMul y, rfl⟩
      have hqE : q ∈ E := (hEmem q).mpr hy
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf D) q
      have huFp : (u : P) ∈ Fp := by
        rw [hFp]; exact Subgroup.mem_map.mpr ⟨u, (hEmem2 u).mpr hqE, rfl⟩
      rw [hFA] at huFp
      have hq1 : QuotientGroup.mk' (A.subgroupOf D) u = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_subgroupOf.mpr huFp)
      rw [hq1, ofMul_one]
    · right
      rw [Submodule.eq_top_iff']
      intro y
      obtain ⟨q, rfl⟩ : ∃ q, Additive.ofMul q = y := ⟨Additive.toMul y, rfl⟩
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf D) q
      have huFp : (u : P) ∈ Fp := by rw [hFD]; exact u.2
      rw [hFp] at huFp
      obtain ⟨u', hu', hu'eq⟩ := Subgroup.mem_map.mp huFp
      have h1 : u' = u := D.subtype_injective hu'eq
      rw [← h1]
      exact (hEmem (QuotientGroup.mk' (A.subgroupOf D) u')).mp ((hEmem2 u').mp hu')
  -- ## The linear map `Ψ : V → End_{𝔽₂}(GF(2^n))`
  let EndF := GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n
  let Ψfun : (↥D ⧸ (A.subgroupOf D)) → EndF := fun v =>
    AddMonoidHom.toZModLinearMap 2
      { toFun := PsiFun v, map_zero' := hPsi0 v, map_add' := hPsiadd v }
  have hΨfun_apply : ∀ v x, Ψfun v x = PsiFun v x := fun v x => rfl
  have hΨfun_add : ∀ v w, Ψfun (v * w) = Ψfun v + Ψfun w := by
    intro v w
    ext x
    rw [hΨfun_apply, LinearMap.add_apply, hΨfun_apply, hΨfun_apply]
    exact hPsimul v w x
  have hΨfun_one : Ψfun 1 = 0 := by
    ext x
    rw [hΨfun_apply, LinearMap.zero_apply]
    exact hPsi_one x
  let Ψadd : V →+ EndF :=
    { toFun := fun v => Ψfun (Additive.toMul v)
      map_zero' := by
        show Ψfun (Additive.toMul (0 : V)) = 0
        rw [show Additive.toMul (0 : V) = 1 from rfl]
        exact hΨfun_one
      map_add' := by
        intro v w
        show Ψfun (Additive.toMul (v + w)) = Ψfun (Additive.toMul v) + Ψfun (Additive.toMul w)
        rw [toMul_add]
        exact hΨfun_add _ _ }
  let Ψ : V →ₗ[ZMod 2] EndF := AddMonoidHom.toZModLinearMap 2 Ψadd
  have hΨ_apply : ∀ (v : (↥D ⧸ (A.subgroupOf D))) x, Ψ (Additive.ofMul v) x = PsiFun v x := by
    intro v x
    show Ψadd (Additive.ofMul v) x = PsiFun v x
    rfl
  have hΨinj : Function.Injective Ψ := by
    intro v w hvw
    have h1 : ∀ x, PsiFun (Additive.toMul (v - w)) x = 0 := by
      intro x
      have h2 : Ψ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
      have h3 : Ψ (v - w) x = 0 := by rw [h2]; rfl
      have h4 : Ψ (Additive.ofMul (Additive.toMul (v - w))) x = 0 := h3
      rwa [hΨ_apply] at h4
    have h5 : Additive.toMul (v - w) = 1 := hPsiinj _ h1
    have h6 : v - w = 0 := by
      have h7 := congrArg Additive.ofMul h5
      rw [ofMul_one] at h7
      simpa using h7
    exact sub_eq_zero.mp h6
  have hΨeq : ∀ v : V, Ψ (ξV v) = Work.Higman.H8.FSB.singAct νU (Ψ v) := by
    intro v
    obtain ⟨v', rfl⟩ : ∃ v' : (↥D ⧸ (A.subgroupOf D)), Additive.ofMul v' = v :=
      ⟨Additive.toMul v, rfl⟩
    ext x
    rw [Work.Higman.H8.FSB.singAct_apply, Work.Higman.H8.conjAction_apply,
      Units.val_inv_eq_inv_val]
    show Ψ (ξV (Additive.ofMul v')) x
      = (νU : GaloisField 2 n) * Ψ (Additive.ofMul v') ((νU : GaloisField 2 n)⁻¹ * x)
    rw [hξV_apply, hΨ_apply, hΨ_apply]
    exact hPsixi v' x
  -- ## Apply the abstract layer lemma
  obtain ⟨k, hk, φlin, hφlin0, hφlinxi, hφlinsurj⟩ :=
    Work.Higman.H8.layer_of_end_injection hn2 νU hνord hVcard ξV hsimple Ψ hΨinj hΨeq
  -- ## The coordinate function on `P`
  let φ : P → GaloisField 2 n := fun c =>
    if hc : c ∈ D then φlin (Additive.ofMul (QuotientGroup.mk (⟨c, hc⟩ : ↥D))) else 0
  have hφ_apply : ∀ (c : P) (hc : c ∈ D),
      φ c = φlin (Additive.ofMul (QuotientGroup.mk (⟨c, hc⟩ : ↥D))) := by
    intro c hc
    simp only [φ, dif_pos hc]
  have hlam : ∀ k : ℕ, Work.Higman.H8.lam νU k = (νU : GaloisField 2 n) ^ (1 - (2 : ℤ) ^ k) := by
    intro k
    rw [Work.Higman.H8.lam,
      show (1 : ℤ) - (2 : ℤ) ^ k = 1 + (-((2 : ℤ) ^ k)) from by ring,
      zpow_add₀ (Units.ne_zero νU), zpow_one, zpow_neg,
      show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) from by push_cast; ring, zpow_natCast]
  have hνord' : orderOf ((νU : GaloisField 2 n)) = 2 ^ n - 1 := by
    rw [orderOf_units]; exact hνord
  refine ⟨n, GaloisField 2 n, inferInstance, Work.Higman.H8.galoisFintype, Work.Higman.H8.galoisDecEq,
    inferInstance, (νU : GaloisField 2 n), k, φ, ?_, hn2, hνord', hk, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card, Work.Higman.H8.card_galois (by omega)]
  · intro c c' hc hc'
    have h3 : c * c' ∈ D := D.mul_mem hc hc'
    rw [hφ_apply (c * c') h3, hφ_apply c hc, hφ_apply c' hc']
    have hmk : (QuotientGroup.mk (⟨c * c', h3⟩ : ↥D) : (↥D ⧸ (A.subgroupOf D)))
        = QuotientGroup.mk (⟨c, hc⟩ : ↥D) * QuotientGroup.mk (⟨c', hc'⟩ : ↥D) := rfl
    rw [hmk, ofMul_mul, map_add]
  · intro c hc
    rw [hφ_apply c hc, hφlin0]
    constructor
    · intro h
      have h1 : (QuotientGroup.mk (⟨c, hc⟩ : ↥D) : (↥D ⧸ (A.subgroupOf D))) = 1 :=
        ofMul_eq_zero.mp h
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (N := A.subgroupOf D) (⟨c, hc⟩ : ↥D)).mp h1)
    · intro h
      have h1 : (QuotientGroup.mk (⟨c, hc⟩ : ↥D) : (↥D ⧸ (A.subgroupOf D))) = 1 :=
        (QuotientGroup.eq_one_iff (N := A.subgroupOf D) (⟨c, hc⟩ : ↥D)).mpr
          (Subgroup.mem_subgroupOf.mpr h)
      rw [h1, ofMul_one]
  · intro c hc
    have hξc : h.xi c ∈ D := by
      have h1 : h.xi c ∈ D.map (h.xi : MulAut P).toMonoidHom := Subgroup.mem_map_of_mem _ hc
      rwa [hDinv] at h1
    rw [hφ_apply (h.xi c) hξc, hφ_apply c hc]
    have hmk : (QuotientGroup.mk (⟨h.xi c, hξc⟩ : ↥D) : (↥D ⧸ (A.subgroupOf D)))
        = ξD (QuotientGroup.mk (⟨c, hc⟩ : ↥D)) := by
      rw [hξD_mk]
      exact congrArg (fun x : ↥D => (QuotientGroup.mk x : (↥D ⧸ (A.subgroupOf D))))
        (Subtype.ext (Work.Higman.MSA.xiSubAut_apply h hDinv ⟨c, hc⟩).symm)
    rw [hmk, ← hξV_apply, hφlinxi, hlam k]
  · intro x
    obtain ⟨v, hv⟩ := hφlinsurj x
    obtain ⟨q, rfl⟩ : ∃ q : (↥D ⧸ (A.subgroupOf D)), Additive.ofMul q = v :=
      ⟨Additive.toMul v, rfl⟩
    obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective q
    refine ⟨(d : P), d.2, ?_⟩
    rw [hφ_apply (d : P) d.2]
    have hdd : (QuotientGroup.mk (⟨(d : P), d.2⟩ : ↥D) : (↥D ⧸ (A.subgroupOf D))) = q := hd
    rw [hdd]
    exact hv

end Work.Higman.HS
