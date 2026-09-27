import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspCorrDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.parabolicCommuteFix
import Submission.Work.Mostow.cuspStabFlatAction
import Submission.Work.Mostow.horoActTrivId

/-!
# The cusp correspondence (`Work.Mostow.cuspCorr`)

An abstract isomorphism `f : Γ ≃* Λ` of lattices in `PO(n,1)` induces an `f`-equivariant
bijection `F` between the parabolic fixed point sets (`parFixSet`) of `Γ` and `Λ` whose point
stabilisers correspond exactly (conditions 2 and 3 of the statement).

Chapters: boundary calculus (`bd_inv_bd_cuspCorr`, `bd_conj_fixes`); commuting with a parabolic
(`abelian_fixes`); virtually abelian groups of isometries (`virtAbelian_fixes`); cusp
stabilisers preserve horospheres (`cuspStab_levels`); cusp stabilisers are virtually abelian
(`cuspStab_virtAbelian`, from the delegated geometric chapters `horoActTrivId` and
`cuspStabFlatAction`); the cusp correspondence (`cuspImage_exists`); the two directions of the
stabiliser correspondence (`cuspStab_corr`, `cuspStab_corr_rev`); and the assembly (`cuspCorr`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Tools inlined to keep the dependency footprint small -/

/-- `busemann ξ (sinh t • ξ) = -t` for `ξ` on the boundary sphere. -/
lemma busemann_sinh_smul {ξ : E n} (hξ : ξ ∈ Sph n) (t : ℝ) :
    busemann ξ (Real.sinh t • ξ) = -t := by
  have hξn : ‖ξ‖ = 1 := by
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have h1 : tpart (Real.sinh t • ξ) = Real.cosh t := by
    have hnorm : ‖Real.sinh t • ξ‖ ^ 2 = Real.sinh t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hξn, mul_one, sq_abs]
    rw [tpart, hnorm]
    have h2 : 1 + Real.sinh t ^ 2 = Real.cosh t ^ 2 := by rw [Real.cosh_sq]; ring
    rw [h2, Real.sqrt_sq (le_of_lt (Real.cosh_pos t))]
  have h3 : inner ℝ (Real.sinh t • ξ) ξ = Real.sinh t := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hξn]
    ring
  rw [busemann, h1, h3]
  rw [← Real.log_exp (-t)]
  congr 1
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-! ## Boundary calculus -/

/-- `bd g⁻¹ (bd g ξ) = ξ` on the boundary sphere. -/
lemma bd_inv_bd_cuspCorr (hA : POBasic n) {g : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g⁻¹ (bd g ξ) = ξ := by
  have h : bd (g⁻¹ * g) ξ = bd g⁻¹ (bd g ξ) := hA.bd_mul g⁻¹ g ξ hξ
  rw [inv_mul_cancel, hA.bd_one ξ hξ] at h
  exact h.symm

/-- `bd g (bd g⁻¹ ξ) = ξ` on the boundary sphere. -/
lemma bd_bd_inv (hA : POBasic n) {g : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g (bd g⁻¹ ξ) = ξ := by
  have h : bd (g * g⁻¹) ξ = bd g (bd g⁻¹ ξ) := hA.bd_mul g g⁻¹ ξ hξ
  rw [mul_inv_cancel, hA.bd_one ξ hξ] at h
  exact h.symm

/-- `g p g⁻¹` fixes `bd g ξ` whenever `p` fixes `ξ`. -/
lemma bd_conj_fixes (hA : POBasic n) {g p : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n)
    (hp : bd p ξ = ξ) : bd (g * p * g⁻¹) (bd g ξ) = bd g ξ := by
  have hmem : bd g ξ ∈ Sph n := hA.bd_mem g ξ hξ
  have hmem2 : bd g⁻¹ (bd g ξ) ∈ Sph n := hA.bd_mem g⁻¹ (bd g ξ) hmem
  calc bd (g * p * g⁻¹) (bd g ξ)
      = bd g (bd p (bd g⁻¹ (bd g ξ))) := by
        rw [hA.bd_mul (g * p) g⁻¹ (bd g ξ) hmem,
            hA.bd_mul g p (bd g⁻¹ (bd g ξ)) hmem2]
    _ = bd g (bd p ξ) := by rw [bd_inv_bd_cuspCorr hA hξ]
    _ = bd g ξ := by rw [hp]

/-! ## Commuting with a parabolic -/

/-- An isometry commuting with a parabolic `p` fixes the (unique) boundary fixed point of `p`. -/
theorem abelian_fixes (hA : POActionProp n) (hI : HypIsometryProp n)
    {g p : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n) (hp : IsParabolic p) (hpξ : bd p ξ = ξ)
    (hcomm : g * p = p * g) : bd g ξ = ξ := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hgξ : bd g ξ ∈ Sph n := hA'.bd_mem g ξ hξ
  have hconj : g * p * g⁻¹ = p := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : bd p (bd g ξ) = bd g ξ := by
    have h2 := bd_conj_fixes hA' (g := g) (p := p) hξ hpξ
    rwa [hconj] at h2
  exact paraUniqueFixed hA' hI' hp hξ hpξ hgξ hfix

/-- A group of isometries that has an abelian set `A` closed under conjugation, containing
positive powers of all its elements, and contains a parabolic `p`, is contained in the stabiliser
of the fixed point of `p`. -/
theorem virtAbelian_fixes (hA : POActionProp n) (hI : HypIsometryProp n)
    {H : Set (PO n 1)} (hHmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    {p : PO n 1} (hp : IsParabolic p) (hpH : p ∈ H)
    {ξ : E n} (hξ : ξ ∈ Sph n) (hpξ : bd p ξ = ξ)
    {A : Set (PO n 1)} (hAH : ∀ a ∈ A, a ∈ H)
    (hAnorm : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAfin : ∃ k : ℕ, 0 < k ∧ ∀ h ∈ H, h ^ k ∈ A) :
    ∀ x ∈ H, bd x ξ = ξ := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨k, hk, hpow⟩ := hAfin
  have hpk : p ^ k ∈ A := hpow p hpH
  have hpkpar : IsParabolic (p ^ k) := pcf_parabolic_pow hA hI p hp k hk
  have hpkξ : bd (p ^ k) ξ = ξ := pcf_bd_pow_fixed hA p ξ hξ hpξ k
  have hAfix : ∀ a ∈ A, bd a ξ = ξ := by
    intro a ha
    have hcomm : a * (p ^ k) = (p ^ k) * a := hAab a ha (p ^ k) hpk
    exact abelian_fixes hA hI hξ hpkpar hpkξ hcomm
  intro x hx
  have hconj : x * (p ^ k) * x⁻¹ ∈ A := hAnorm x hx (p ^ k) hpk
  have hconjfix : bd (x * (p ^ k) * x⁻¹) ξ = ξ := hAfix _ hconj
  have hpar : IsParabolic (x * (p ^ k) * x⁻¹) := isParabolic_conj hA hI x (p ^ k) hpkpar
  have hbdx : bd x ξ ∈ Sph n := hA'.bd_mem x ξ hξ
  have hfixx : bd (x * (p ^ k) * x⁻¹) (bd x ξ) = bd x ξ := bd_conj_fixes hA' hξ hpkξ
  exact paraUniqueFixed hA' hI' hpar hξ hconjfix hbdx hfixx

/-- Every real value is attained by the Busemann function at `ξ`. -/
lemma busemann_surjective {ξ : E n} (hξ : ξ ∈ Sph n) (y : ℝ) :
    ∃ u : E n, busemann ξ u = y :=
  ⟨Real.sinh (-y) • ξ, by rw [busemann_sinh_smul hξ]; ring⟩

/-- If `g` fixes `ξ` and preserves the horoball of level `t` at `ξ`, then its Busemann cocycle
at `ξ` vanishes. -/
lemma cocycle_zero_of_horoball (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (hg : bd g ξ = ξ) (t c : ℝ)
    (hhor : ∀ u : E n, g • u ∈ horoball ξ t ↔ u ∈ horoball ξ t)
    (hc : ∀ u : E n, busemann ξ (g • u) = busemann ξ u + c) :
    c = 0 := by
  by_contra hne
  have hkey : ∀ u : E n, (busemann ξ u < t - c) ↔ (busemann ξ u < t) := by
    intro u
    have h1 : busemann ξ u + c < t ↔ busemann ξ u < t := by
      have h2 := hhor u
      simpa only [horoball, Set.mem_ofPred_eq, hc u] using h2
    rw [← h1]
    constructor <;> intro h <;> linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨u, hu⟩ := busemann_surjective hξ (t - c / 2)
    have h1 : busemann ξ u < t - c := by rw [hu]; linarith
    have h2 : ¬ (busemann ξ u < t) := by rw [hu]; linarith
    exact h2 ((hkey u).mp h1)
  · obtain ⟨u, hu⟩ := busemann_surjective hξ (t - c / 2)
    have h1 : busemann ξ u < t := by rw [hu]; linarith
    have h2 : ¬ (busemann ξ u < t - c) := by rw [hu]; linarith
    exact h2 ((hkey u).mpr h1)

/-! ## The stabiliser of a cusp preserves the horospheres -/

/-- For a cusp `ξ` of a lattice `Γ`, the whole stabiliser `Γ_ξ` preserves every horosphere at
`ξ` (equivalently, the Busemann cocycle vanishes on `Γ_ξ`). -/
theorem cuspStab_levels (hA : POActionProp n) (hI : HypIsometryProp n)
    (hG : GeomFiniteProp n) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    {ξ : E n} (hξ : ξ ∈ parFixSet Γ) {γ : Γ} (hγ : bd (γ : PO n 1) ξ = ξ) :
    ∀ u : E n, lev ξ ((γ : PO n 1) • u) = lev ξ u := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨hξS, δ, hδpar, hδfix⟩ := hξ
  obtain ⟨P, ht, hPsub, hPinv, hHeq, hPdisj, hKc, hCuspC, hPpar, hPall⟩ := hG Γ hΓ
  have hξP : ξ ∈ P := by
    obtain ⟨ξ₀, hξ₀P, hξ₀fix⟩ := hPall δ hδpar
    have h1 : ξ₀ = ξ :=
      paraUniqueFixed hA' hI' hδpar hξS hδfix (hPsub hξ₀P) hξ₀fix
    rwa [h1] at hξ₀P
  have hhor : ∀ u : E n, (γ : PO n 1) • u ∈ horoball ξ (ht ξ) ↔ u ∈ horoball ξ (ht ξ) := by
    intro u
    have h := hHeq γ ξ hξP u
    rwa [hγ] at h
  have hcoc : ∀ u : E n, busemann ξ ((γ : PO n 1) • u)
      = busemann ξ u + busemann ξ ((γ : PO n 1) • (0 : E n)) := by
    intro u
    have h := hI'.busemann_cocycle (γ : PO n 1) ξ u hξS
    rwa [hγ] at h
  have hc := cocycle_zero_of_horoball hA hI (γ : PO n 1) ξ hξS hγ (ht ξ)
    (busemann ξ ((γ : PO n 1) • (0 : E n))) hhor hcoc
  intro u
  rw [lev_eq_exp hξS ((γ : PO n 1) • u), lev_eq_exp hξS u, hcoc u, hc, add_zero]

/-! ## The stabiliser of a cusp is virtually abelian -/

/-- **The stabiliser of a cusp of a lattice is virtually abelian**, in the concrete form used
below: an abelian set `A` of stabiliser elements, closed under conjugation by the stabiliser and
containing a positive power of every stabiliser element. -/
theorem cuspStab_virtAbelian (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (hG : GeomFiniteProp n)
    (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) {ξ : E n} (hξ : ξ ∈ parFixSet Γ) :
    ∃ A : Set (PO n 1),
      (∀ a ∈ A, a ∈ Γ ∧ bd a ξ = ξ) ∧
      (∀ h ∈ Γ, bd h ξ = ξ → ∀ a ∈ A, h * a * h⁻¹ ∈ A) ∧
      (∃ k : ℕ, 0 < k ∧ ∀ h ∈ Γ, bd h ξ = ξ → h ^ k ∈ A) ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨hξS, δ, hδpar, hδfix⟩ := hξ
  have hξ' : ξ ∈ parFixSet Γ := ⟨hξS, δ, hδpar, hδfix⟩
  obtain ⟨P, ht, hPsub, hPinv, hHeq, hPdisj, hKc, hCuspC, hPpar, hPall⟩ := hG Γ hΓ
  have hξP : ξ ∈ P := by
    obtain ⟨ξ₀, hξ₀P, hξ₀fix⟩ := hPall δ hδpar
    have h1 : ξ₀ = ξ :=
      paraUniqueFixed hA' hI' hδpar hξS hδfix (hPsub hξ₀P) hξ₀fix
    rwa [h1] at hξ₀P
  have hlev : ∀ (γ : Γ) (u : E n), bd (γ : PO n 1) ξ = ξ →
      lev ξ ((γ : PO n 1) • u) = lev ξ u :=
    fun γ u hγ => cuspStab_levels hA hI hG Γ hΓ hξ' hγ u
  have hD : 0 < Real.exp (ht ξ) := Real.exp_pos _
  have hcoc : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = Real.exp (ht ξ) →
      ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K := by
    obtain ⟨K, hKc, hK⟩ := hCuspC ξ hξP
    refine ⟨K, hKc, fun u hu => ?_⟩
    refine hK u ?_
    have h2 : lev ξ u = Real.exp (busemann ξ u) := lev_eq_exp hξS u
    rw [h2] at hu
    exact Real.exp_injective hu
  obtain ⟨m, ρ, hpd, hcocρ, htriv⟩ :=
    cuspStabFlatAction hA hI Γ ξ hξS (Real.exp (ht ξ)) hD hlev hΓ.1 hcoc
  obtain ⟨T, v, hTfin, hTtrans, hTspan⟩ :=
    hBb m (cuspStab hA' Γ ξ hξS) ρ hpd hcocρ
  haveI : T.FiniteIndex := hTfin
  -- the kernel of the flat action acts trivially on the horosphere, hence is trivial
  have hcoe_mul : ∀ a b : cuspStab hA' Γ ξ hξS,
      ((a * b : cuspStab hA' Γ ξ hξS) : PO n 1)
        = (a : PO n 1) * (b : PO n 1) := by
    intro a b
    exact map_mul (Subgroup.subtype Γ) a.1 b.1
  have hcoe_inv : ∀ a : cuspStab hA' Γ ξ hξS,
      ((a⁻¹ : cuspStab hA' Γ ξ hξS) : PO n 1) = ((a : PO n 1))⁻¹ := by
    intro a
    exact map_inv (Subgroup.subtype Γ) a.1
  have hcoe_pow : ∀ (a : cuspStab hA' Γ ξ hξS) (k : ℕ),
      ((a ^ k : cuspStab hA' Γ ξ hξS) : PO n 1) = ((a : PO n 1)) ^ k := by
    intro a k
    exact map_pow (Subgroup.subtype Γ) a.1 k
  have hfaith : ∀ g : cuspStab hA' Γ ξ hξS, (∀ x : E m, ρ g x = x) → g = 1 := by
    intro g hg
    have hg' : bd ((g : cuspStab hA' Γ ξ hξS) : PO n 1) ξ = ξ :=
      (mem_cuspStab (hA := hA') (Γ := Γ) (ξ := ξ) (hξ := hξS) g).mp g.2
    have h1 : ((g : cuspStab hA' Γ ξ hξS) : PO n 1) = 1 := by
      refine horoActTrivId hA ((g : cuspStab hA' Γ ξ hξS) : PO n 1) ξ hξS
        (Real.exp (ht ξ)) hD hg' ?_ ?_
      · intro u
        exact cuspStab_levels hA hI hG Γ hΓ hξ' hg' u
      · intro u hu
        have h2 : ((((g : cuspStab hA' Γ ξ hξS) : Γ) : PO n 1)) • u = u := htriv g hg u hu
        exact h2
    have h2 : (g : Γ) = 1 := Subtype.ext h1
    exact Subtype.ext h2
  -- `T` is abelian
  have hTcomm : ∀ a b : cuspStab hA' Γ ξ hξS, a ∈ T → b ∈ T → a * b = b * a := by
    intro a b ha hb
    have hρab : ρ (a * b) = ρ (b * a) := by
      apply IsometryEquiv.ext
      intro x
      rw [map_mul, map_mul, IsometryEquiv.mul_apply, IsometryEquiv.mul_apply,
        hTtrans a ha x, hTtrans b hb (x + v a), hTtrans b hb x, hTtrans a ha (x + v b)]
      abel
    have hker : ρ ((a * b) * (b * a)⁻¹) = 1 := by
      rw [map_mul, map_inv, hρab, mul_inv_cancel]
    have h1 : (a * b) * (b * a)⁻¹ = 1 := hfaith _ (fun x => by rw [hker]; rfl)
    exact mul_inv_eq_one.mp h1
  refine ⟨{x : PO n 1 | ∃ t : cuspStab hA' Γ ξ hξS, t ∈ T.normalCore ∧ (t : PO n 1) = x},
    ?_, ?_, ?_, ?_⟩
  · rintro a ⟨t, ht, rfl⟩
    exact ⟨t.1.2, (mem_cuspStab (hA := hA') (Γ := Γ) (ξ := ξ) (hξ := hξS) t.1).mp t.2⟩
  · rintro h hΓ hfix a ⟨t, ht, rfl⟩
    let hcG : Γ := ⟨h, hΓ⟩
    let hc : cuspStab hA' Γ ξ hξS := ⟨hcG, hfix⟩
    have htc : hc * t * hc⁻¹ ∈ T.normalCore :=
      (inferInstance : (T.normalCore).Normal).conj_mem t ht hc
    refine ⟨hc * t * hc⁻¹, htc, ?_⟩
    simp only [hcoe_mul, hcoe_inv, hc, hcG]
  · refine ⟨T.normalCore.index, Nat.pos_of_ne_zero ?_, ?_⟩
    · exact (inferInstance : T.normalCore.FiniteIndex).index_ne_zero
    · intro h hΓ hfix
      let hcG : Γ := ⟨h, hΓ⟩
      let hc : cuspStab hA' Γ ξ hξS := ⟨hcG, hfix⟩
      refine ⟨hc ^ T.normalCore.index,
        Subgroup.pow_index_mem T.normalCore hc, ?_⟩
      simp only [hcoe_pow, hc, hcG]
  · rintro a ⟨ta, hta, rfl⟩ b ⟨tb, htb, rfl⟩
    have h1 : ta * tb = tb * ta := hTcomm ta tb (T.normalCore_le hta) (T.normalCore_le htb)
    have h2 := congrArg (fun t : cuspStab hA' Γ ξ hξS => ((t : Γ) : PO n 1)) h1
    rw [hcoe_mul ta tb, hcoe_mul tb ta] at h2
    exact h2

/-! ## The cusp correspondence -/

/-- Two parabolic elements of a lattice fixing the same cusp have commuting positive powers. -/
theorem parabolics_commute_powers (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (hG : GeomFiniteProp n)
    (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) {ξ : E n} (hξ : ξ ∈ parFixSet Γ)
    {p q : PO n 1} (hpΓ : p ∈ Γ) (hqΓ : q ∈ Γ) (hp : IsParabolic p) (hq : IsParabolic q)
    (hpξ : bd p ξ = ξ) (hqξ : bd q ξ = ξ) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧ p ^ m * q ^ k = q ^ k * p ^ m := by
  obtain ⟨A, hAmem, hAnorm, ⟨k, hk, hpow⟩, hAab⟩ := cuspStab_virtAbelian hA hI hBb hG Γ hΓ hξ
  exact ⟨k, k, hk, hk, hAab _ (hpow p hpΓ hpξ) _ (hpow q hqΓ hqξ)⟩

/-- **The forward cusp correspondence.**  For a cusp `ξ` of `Γ` there is a unique parabolic
fixed point of `Λ` that is fixed by the image under `f` of the whole stabiliser of `ξ`. -/
theorem cuspImage_exists (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (hG : GeomFiniteProp n) (hC : CuspRecognitionProp n)
    {Γ Λ : Subgroup (PO n 1)} (hΓ : HypLattice Γ) (hΛ : HypLattice Λ) (f : Γ ≃* Λ)
    {ξ : E n} (hξ : ξ ∈ parFixSet Γ) :
    ∃! η : E n,
      η ∈ parFixSet Λ ∧ ∀ γ : Γ,
        bd ((γ : Γ) : PO n 1) ξ = ξ → bd (((f γ : Λ)) : PO n 1) η = η := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨hξS, p, hppar, hpξ⟩ := hξ
  obtain ⟨PΛ, htΛ, hPΛsub, hPΛinv, hPΛheq, hPΛdisj, hPΛK, hPΛcoc, hPΛpar, hPΛall⟩ := hG Λ hΛ
  have hfppar : IsParabolic (((f p : Λ)) : PO n 1) := hC Γ Λ hΓ hΛ f p hppar
  obtain ⟨η, hηP, hηfix⟩ := hPΛall (f p) hfppar
  have hηS : η ∈ Sph n := hPΛsub hηP
  -- every parabolic element of the stabiliser of `ξ` maps to an element fixing `η`
  have hcruce : ∀ q : Γ, IsParabolic ((q : Γ) : PO n 1) → bd ((q : Γ) : PO n 1) ξ = ξ →
      bd (((f q : Λ)) : PO n 1) η = η := by
    intro q hq hqξ
    obtain ⟨m, k, hm, hk, hcomm⟩ :=
      parabolics_commute_powers hA hI hBb hG Γ hΓ ⟨hξS, p, hppar, hpξ⟩
        q.2 p.2 hq hppar hqξ hpξ
    have hcommG : (q ^ m * p ^ k : Γ) = p ^ k * q ^ m := by
      apply Subtype.ext
      simpa [Subgroup.coe_mul, Subgroup.coe_pow] using hcomm
    have hcomm' : (((f q : Λ)) : PO n 1) ^ m * (((f p : Λ)) : PO n 1) ^ k
        = (((f p : Λ)) : PO n 1) ^ k * (((f q : Λ)) : PO n 1) ^ m := by
      have h1 : ((f (q ^ m * p ^ k) : Λ) : PO n 1)
          = (((f q : Λ)) : PO n 1) ^ m * (((f p : Λ)) : PO n 1) ^ k := by
        rw [map_mul, map_pow, map_pow]; rfl
      have h2 : ((f (p ^ k * q ^ m) : Λ) : PO n 1)
          = (((f p : Λ)) : PO n 1) ^ k * (((f q : Λ)) : PO n 1) ^ m := by
        rw [map_mul, map_pow, map_pow]; rfl
      have h3 : ((f (q ^ m * p ^ k) : Λ) : PO n 1) = ((f (p ^ k * q ^ m) : Λ) : PO n 1) := by
        rw [hcommG]
      rw [h1, h2] at h3
      exact h3
    obtain ⟨η', hη'P, hη'fix⟩ := hPΛall (f q) (hC Γ Λ hΓ hΛ f q hq)
    have hη'S : η' ∈ Sph n := hPΛsub hη'P
    have hsame : η' = η :=
      parabolicCommuteFix n hn hA hI (((f q : Λ)) : PO n 1) (((f p : Λ)) : PO n 1)
        (hC Γ Λ hΓ hΛ f q hq) hfppar η' η hη'S hηS hη'fix hηfix m k hm hk hcomm'
    rwa [hsame] at hη'fix
  refine ⟨η, ⟨⟨hηS, f p, hfppar, hηfix⟩, ?_⟩, ?_⟩
  · intro γ hγ
    have hconjpar : IsParabolic (((γ : Γ) : PO n 1) * (p : PO n 1) * (((γ : Γ) : PO n 1))⁻¹) :=
      isParabolic_conj hA hI ((γ : Γ) : PO n 1) (p : PO n 1) hppar
    have hconjξ : bd (((γ : Γ) : PO n 1) * (p : PO n 1) * (((γ : Γ) : PO n 1))⁻¹) ξ = ξ := by
      have h2 := bd_conj_fixes hA' (g := ((γ : Γ) : PO n 1)) (p := (p : PO n 1)) hξS hpξ
      rwa [hγ] at h2
    have hconjfix : bd (((f (γ * p * γ⁻¹) : Λ)) : PO n 1) η = η := by
      have h1 : ((γ * p * γ⁻¹ : Γ) : PO n 1)
          = ((γ : Γ) : PO n 1) * (p : PO n 1) * (((γ : Γ) : PO n 1))⁻¹ := by
        simp [Subgroup.coe_mul, Subgroup.coe_inv]
      have hpar : IsParabolic (((γ * p * γ⁻¹ : Γ)) : PO n 1) := by
        rw [h1]; exact hconjpar
      have hfix : bd (((γ * p * γ⁻¹ : Γ)) : PO n 1) ξ = ξ := by
        rw [h1]; exact hconjξ
      exact hcruce (γ * p * γ⁻¹) hpar hfix
    have hcoe : (((f (γ * p * γ⁻¹) : Λ)) : PO n 1)
        = (f γ : PO n 1) * (f p : PO n 1) * (f γ : PO n 1)⁻¹ := by
      have h1 : f (γ * p * γ⁻¹) = f γ * f p * (f γ)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      simpa using congrArg (fun t : Λ => ((t : Λ) : PO n 1)) h1
    rw [hcoe] at hconjfix
    have hpar2 : IsParabolic ((f γ : PO n 1) * (f p : PO n 1) * (f γ : PO n 1)⁻¹) :=
      isParabolic_conj hA hI (f γ : PO n 1) (f p : PO n 1) hfppar
    have hfixx : bd ((f γ : PO n 1) * (f p : PO n 1) * (f γ : PO n 1)⁻¹) (bd (f γ : PO n 1) η)
        = bd (f γ : PO n 1) η :=
      bd_conj_fixes hA' (g := (f γ : PO n 1)) (p := (f p : PO n 1)) hηS hηfix
    have hbdfγ : bd (f γ : PO n 1) η ∈ Sph n := hA'.bd_mem (f γ : PO n 1) η hηS
    exact paraUniqueFixed hA' hI' hpar2 hηS hconjfix hbdfγ hfixx
  · intro η' hη'
    have h1 : bd (((f p : Λ)) : PO n 1) η' = η' := hη'.2 p hpξ
    exact paraUniqueFixed hA' hI' hfppar hηS hηfix hη'.1.1 h1

/-- **The stabiliser correspondence (onto).**  Given that the image of `Γ_ξ` lies in `Λ_η`, every
element of `Λ_η` is the image of an element of `Γ_ξ`. -/
theorem cuspStab_corr (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (hG : GeomFiniteProp n)
    {Γ Λ : Subgroup (PO n 1)} (hΓ : HypLattice Γ) (hΛ : HypLattice Λ) (f : Γ ≃* Λ)
    {ξ : E n} (hξ : ξ ∈ parFixSet Γ) {η : E n} (hη : η ∈ parFixSet Λ)
    (hfwd : ∀ γ : Γ, bd ((γ : Γ) : PO n 1) ξ = ξ → bd (((f γ : Λ)) : PO n 1) η = η) :
    ∀ m : Λ, bd ((m : Λ) : PO n 1) η = η → bd (((f.symm m : Γ)) : PO n 1) ξ = ξ := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨hξS, p₀, hp₀par, hp₀ξ⟩ := hξ
  obtain ⟨A', hA'mem, hA'norm, ⟨k, hk, hA'pow⟩, hA'ab⟩ :=
    cuspStab_virtAbelian hA hI hBb hG Λ hΛ hη
  set H : Set (PO n 1) :=
    {x | ∃ γ : Γ, (γ : PO n 1) = x ∧ bd (((f γ : Λ)) : PO n 1) η = η} with hHdef
  set A : Set (PO n 1) :=
    {x | ∃ γ : Γ, (γ : PO n 1) = x ∧ (((f γ : Λ)) : PO n 1) ∈ A'} with hAdef
  have hHmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H := by
    rintro a ⟨γ, rfl, hγ⟩ b ⟨δ, rfl, hδ⟩
    refine ⟨γ * δ, by simp, ?_⟩
    have h1 : (((f (γ * δ) : Λ)) : PO n 1)
        = (((f γ : Λ)) : PO n 1) * (((f δ : Λ)) : PO n 1) := by
      rw [map_mul]; rfl
    rw [h1, hA'.bd_mul _ _ η hη.1, hδ, hγ]
  have hAH : ∀ a ∈ A, a ∈ H := by
    rintro a ⟨γ, rfl, hγ⟩
    exact ⟨γ, rfl, (hA'mem _ hγ).2⟩
  have hAnorm : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A := by
    rintro h ⟨γ, rfl, hγ⟩ a ⟨δ, rfl, hδ⟩
    refine ⟨γ * δ * γ⁻¹, by simp, ?_⟩
    have h1 : (((f (γ * δ * γ⁻¹) : Λ)) : PO n 1)
        = (((f γ : Λ)) : PO n 1) * (((f δ : Λ)) : PO n 1) * (((f γ : Λ)) : PO n 1)⁻¹ := by
      rw [map_mul, map_mul, map_inv]; rfl
    rw [h1]
    exact hA'norm _ (f γ).2 hγ _ hδ
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro a ⟨γ, rfl, hγ⟩ b ⟨δ, rfl, hδ⟩
    have h2 : ((f γ : Λ)) * ((f δ : Λ)) = ((f δ : Λ)) * ((f γ : Λ)) := by
      apply Subtype.ext
      simpa [Subgroup.coe_mul] using hA'ab _ hγ _ hδ
    have h3 : (γ * δ : Γ) = δ * γ := f.injective (by rw [map_mul, map_mul, h2])
    have h4 : ((γ * δ : Γ) : PO n 1) = ((δ * γ : Γ) : PO n 1) := congrArg _ h3
    simpa [Subgroup.coe_mul] using h4
  have hAfin : ∃ k : ℕ, 0 < k ∧ ∀ h ∈ H, h ^ k ∈ A := by
    refine ⟨k, hk, ?_⟩
    rintro h ⟨γ, rfl, hγ⟩
    refine ⟨γ ^ k, by simp, ?_⟩
    have h1 : (((f (γ ^ k) : Λ)) : PO n 1) = (((f γ : Λ)) : PO n 1) ^ k := by
      rw [map_pow]; rfl
    rw [h1]
    exact hA'pow _ (f γ).2 hγ
  have hp₀H : (p₀ : PO n 1) ∈ H := ⟨p₀, rfl, hfwd p₀ hp₀ξ⟩
  have hfixall := virtAbelian_fixes hA hI hHmul hp₀par hp₀H hξS hp₀ξ hAH hAnorm hAab hAfin
  intro m hm
  exact hfixall _ ⟨f.symm m, rfl, by simpa using hm⟩

/-- **The stabiliser correspondence (into).**  Given that the preimage of `Λ_η` lies in `Γ_ξ`,
the image of `Γ_χ` lies in `Λ_η`. -/
theorem cuspStab_corr_rev (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (hG : GeomFiniteProp n)
    {Γ Λ : Subgroup (PO n 1)} (hΓ : HypLattice Γ) (hΛ : HypLattice Λ) (f : Γ ≃* Λ)
    {χ : E n} (hχ : χ ∈ parFixSet Γ) {η : E n} (hη : η ∈ parFixSet Λ)
    (hrev : ∀ m : Λ, bd ((m : Λ) : PO n 1) η = η → bd (((f.symm m : Γ)) : PO n 1) χ = χ) :
    ∀ γ : Γ, bd ((γ : Γ) : PO n 1) χ = χ → bd (((f γ : Λ)) : PO n 1) η = η := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨hχS, p₀, hp₀par, hp₀χ⟩ := hχ
  obtain ⟨hηS, q, hqpar, hqη⟩ := hη
  obtain ⟨AΓ, hAΓmem, hAΓnorm, ⟨k, hk, hAΓpow⟩, hAΓab⟩ :=
    cuspStab_virtAbelian hA hI hBb hG Γ hΓ ⟨hχS, p₀, hp₀par, hp₀χ⟩
  set H : Set (PO n 1) :=
    {x | ∃ γ : Γ, (((f γ : Λ)) : PO n 1) = x ∧ bd ((γ : Γ) : PO n 1) χ = χ} with hHdef
  set A : Set (PO n 1) :=
    {x | ∃ γ : Γ, (((f γ : Λ)) : PO n 1) = x ∧ ((γ : Γ) : PO n 1) ∈ AΓ} with hAdef
  have hHmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H := by
    rintro a ⟨γ, rfl, hγ⟩ b ⟨δ, rfl, hδ⟩
    refine ⟨γ * δ, ?_, ?_⟩
    · have h1 : (((f (γ * δ) : Λ)) : PO n 1)
          = (((f γ : Λ)) : PO n 1) * (((f δ : Λ)) : PO n 1) := by
        rw [map_mul]; rfl
      rw [h1]
    · have h1 : ((γ * δ : Γ) : PO n 1)
          = ((γ : Γ) : PO n 1) * ((δ : Γ) : PO n 1) := by
        simp [Subgroup.coe_mul]
      rw [h1, hA'.bd_mul _ _ χ hχS, hδ, hγ]
  have hAH : ∀ a ∈ A, a ∈ H := by
    rintro a ⟨γ, rfl, hγ⟩
    exact ⟨γ, rfl, (hAΓmem _ hγ).2⟩
  have hAnorm : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A := by
    rintro h ⟨γ, rfl, hγ⟩ a ⟨δ, rfl, hδ⟩
    refine ⟨γ * δ * γ⁻¹, ?_, ?_⟩
    · have h1 : (((f (γ * δ * γ⁻¹) : Λ)) : PO n 1)
          = (((f γ : Λ)) : PO n 1) * (((f δ : Λ)) : PO n 1) * (((f γ : Λ)) : PO n 1)⁻¹ := by
        rw [map_mul, map_mul, map_inv]; rfl
      rw [h1]
    · have h1 : ((γ * δ * γ⁻¹ : Γ) : PO n 1)
          = ((γ : Γ) : PO n 1) * ((δ : Γ) : PO n 1) * (((γ : Γ) : PO n 1))⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]; rfl
      rw [h1]
      exact hAΓnorm _ γ.2 hγ _ hδ
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro a ⟨γ, rfl, hγ⟩ b ⟨δ, rfl, hδ⟩
    have h1 : γ * δ = δ * γ :=
      Subtype.ext (by simpa [Subgroup.coe_mul] using hAΓab (γ : PO n 1) hγ (δ : PO n 1) hδ)
    have h2 : ((f γ : Λ)) * ((f δ : Λ)) = ((f δ : Λ)) * ((f γ : Λ)) := by
      rw [← map_mul, ← map_mul, h1]
    simpa [Subgroup.coe_mul] using congrArg (fun t : Λ => ((t : Λ) : PO n 1)) h2
  have hAfin : ∃ k : ℕ, 0 < k ∧ ∀ h ∈ H, h ^ k ∈ A := by
    refine ⟨k, hk, ?_⟩
    rintro h ⟨γ, rfl, hγ⟩
    refine ⟨γ ^ k, ?_, ?_⟩
    · have h1 : (((f (γ ^ k) : Λ)) : PO n 1) = (((f γ : Λ)) : PO n 1) ^ k := by
        rw [map_pow]; rfl
      rw [h1]
    · have h1 : ((γ ^ k : Γ) : PO n 1) = ((γ : Γ) : PO n 1) ^ k := by
        simp [Subgroup.coe_pow]
      rw [h1]
      exact hAΓpow _ γ.2 hγ
  have hqH : (q : PO n 1) ∈ H := ⟨f.symm q, by simp, hrev q hqη⟩
  have hfixall := virtAbelian_fixes hA hI hHmul hqpar hqH hηS hqη hAH hAnorm hAab hAfin
  intro γ hγ
  exact hfixall _ ⟨γ, rfl, hγ⟩

/-- **`Work.Mostow.cuspCorr`.** -/
theorem cuspCorr {n : ℕ} (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (hG : Submission.Mostow.GeomFiniteProp n) (hC : Submission.Mostow.CuspRecognitionProp n)
    {Γ Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hΓ : Submission.Mostow.HypLattice Γ) (hΛ : Submission.Mostow.HypLattice Λ) (f : Γ ≃* Λ) :
    ∃ F : Submission.Mostow.E n → Submission.Mostow.E n,
      (∀ ξ ∈ Work.Mostow.parFixSet Γ, F ξ ∈ Work.Mostow.parFixSet Λ) ∧
      (∀ ξ ∈ Work.Mostow.parFixSet Γ, ∀ γ : Γ,
          Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
          Submission.Mostow.bd ((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) (F ξ) = F ξ) ∧
      (∀ ξ ∈ Work.Mostow.parFixSet Γ, ∀ m : Λ,
          Submission.Mostow.bd ((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) (F ξ) = F ξ →
          ∃ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ
            ∧ f γ = m) ∧
      (∀ ξ ∈ Work.Mostow.parFixSet Γ, ∀ γ : Γ,
          F (Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ)
            = Submission.Mostow.bd ((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) (F ξ)) ∧
      (∀ η ∈ Work.Mostow.parFixSet Λ, ∃ ξ ∈ Work.Mostow.parFixSet Γ, F ξ = η) := by
  classical
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hfwd : ∀ ξ : E n, ξ ∈ parFixSet Γ → ∃! η : E n,
      η ∈ parFixSet Λ ∧ ∀ γ : Γ,
        bd ((γ : Γ) : PO n 1) ξ = ξ → bd (((f γ : Λ)) : PO n 1) η = η :=
    fun ξ hξ => cuspImage_exists hn hA hI hBb hG hC hΓ hΛ f hξ
  have hbwd : ∀ η : E n, η ∈ parFixSet Λ → ∃! ξ : E n,
      ξ ∈ parFixSet Γ ∧ ∀ m : Λ,
        bd ((m : Λ) : PO n 1) η = η → bd (((f.symm m : Γ)) : PO n 1) ξ = ξ :=
    fun η hη => cuspImage_exists hn hA hI hBb hG hC hΛ hΓ f.symm hη
  let F : E n → E n := fun ξ => if h : ξ ∈ parFixSet Γ then (hfwd ξ h).choose else 0
  have hFspec : ∀ ξ (hξ : ξ ∈ parFixSet Γ), F ξ ∈ parFixSet Λ ∧
      ∀ γ : Γ, bd ((γ : Γ) : PO n 1) ξ = ξ → bd (((f γ : Λ)) : PO n 1) (F ξ) = F ξ := by
    intro ξ hξ
    have h := (hfwd ξ hξ).choose_spec.1
    simpa only [F, dif_pos hξ] using h
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ξ hξ => (hFspec ξ hξ).1
  · exact fun ξ hξ γ hγ => (hFspec ξ hξ).2 γ hγ
  · intro ξ hξ m hm
    refine ⟨f.symm m, ?_, by simp⟩
    exact cuspStab_corr hA hI hBb hG hΓ hΛ f hξ (hFspec ξ hξ).1
      (fun γ hγ => (hFspec ξ hξ).2 γ hγ) m hm
  · intro ξ hξ γ
    have hξ' : bd ((γ : Γ) : PO n 1) ξ ∈ parFixSet Γ := parFixSet_smul_mem hA hI hξ
    have hmem : bd (((f γ : Λ)) : PO n 1) (F ξ) ∈ parFixSet Λ :=
      parFixSet_smul_mem hA hI (hFspec ξ hξ).1
    have hfix : ∀ δ : Γ,
        bd ((δ : Γ) : PO n 1) (bd ((γ : Γ) : PO n 1) ξ) = bd ((γ : Γ) : PO n 1) ξ →
        bd (((f δ : Λ)) : PO n 1) (bd (((f γ : Λ)) : PO n 1) (F ξ))
          = bd (((f γ : Λ)) : PO n 1) (F ξ) := by
      intro δ hδ
      have hinner : bd (((γ⁻¹ * δ * γ : Γ)) : PO n 1) ξ = ξ := by
        have h1 : ((γ⁻¹ * δ * γ : Γ) : PO n 1)
            = ((γ : Γ) : PO n 1)⁻¹ * ((δ : Γ) : PO n 1) * ((γ : Γ) : PO n 1) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [h1]
        rw [hA'.bd_mul (((γ : Γ) : PO n 1)⁻¹ * ((δ : Γ) : PO n 1)) ((γ : Γ) : PO n 1) ξ hξ.1]
        rw [hA'.bd_mul ((γ : Γ) : PO n 1)⁻¹ ((δ : Γ) : PO n 1)
              (bd ((γ : Γ) : PO n 1) ξ) (hA'.bd_mem _ ξ hξ.1)]
        rw [hδ]
        exact bd_inv_bd_cuspCorr hA' hξ.1
      have h1 := (hFspec ξ hξ).2 (γ⁻¹ * δ * γ) hinner
      have hcoe : (((f (γ⁻¹ * δ * γ) : Λ)) : PO n 1)
          = (((f γ : Λ)) : PO n 1)⁻¹ * (((f δ : Λ)) : PO n 1) * (((f γ : Λ)) : PO n 1) := by
        have h2 : f (γ⁻¹ * δ * γ) = (f γ)⁻¹ * f δ * f γ := by
          rw [map_mul, map_mul, map_inv]
        simpa using congrArg (fun t : Λ => ((t : Λ) : PO n 1)) h2
      rw [hcoe] at h1
      have h2 : bd (((f γ : Λ)) : PO n 1) (bd (((f γ : Λ) : PO n 1)⁻¹ * ((f δ : Λ) : PO n 1) * ((f γ : Λ) : PO n 1)) (F ξ))
          = bd (((f γ : Λ)) : PO n 1) (F ξ) :=
        congrArg (fun x => bd (((f γ : Λ)) : PO n 1) x) h1
      have h3 : bd (((f γ : Λ)) : PO n 1) (bd (((f γ : Λ) : PO n 1)⁻¹ * ((f δ : Λ) : PO n 1) * ((f γ : Λ) : PO n 1)) (F ξ))
          = bd (((f γ : Λ) : PO n 1) * (((f γ : Λ) : PO n 1)⁻¹ * ((f δ : Λ) : PO n 1) * ((f γ : Λ) : PO n 1))) (F ξ) :=
        (hA'.bd_mul (((f γ : Λ)) : PO n 1)
          ((((f γ : Λ) : PO n 1)⁻¹ * ((f δ : Λ) : PO n 1) * ((f γ : Λ) : PO n 1))) (F ξ)
          ((hFspec ξ hξ).1).1).symm
      have h4 : (((f γ : Λ) : PO n 1) * (((f γ : Λ) : PO n 1)⁻¹ * ((f δ : Λ) : PO n 1) * ((f γ : Λ) : PO n 1)))
          = ((f δ : Λ) : PO n 1) * ((f γ : Λ) : PO n 1) := by group
      have h5 : bd (((f γ : Λ) : PO n 1) * (((f γ : Λ) : PO n 1)⁻¹ * ((f δ : Λ) : PO n 1) * ((f γ : Λ) : PO n 1))) (F ξ)
          = bd (((f δ : Λ) : PO n 1) * ((f γ : Λ) : PO n 1)) (F ξ) := by rw [h4]
      have h6 : bd (((f δ : Λ) : PO n 1) * ((f γ : Λ) : PO n 1)) (F ξ)
          = bd (((f δ : Λ)) : PO n 1) (bd (((f γ : Λ)) : PO n 1) (F ξ)) :=
        hA'.bd_mul (((f δ : Λ)) : PO n 1) (((f γ : Λ)) : PO n 1) (F ξ) ((hFspec ξ hξ).1).1
      exact h6.symm.trans (h5.symm.trans (h3.symm.trans h2))
    exact (hfwd (bd ((γ : Γ) : PO n 1) ξ) hξ').unique (hFspec _ hξ') ⟨hmem, hfix⟩
  · intro η hη
    refine ⟨(hbwd η hη).choose, (hbwd η hη).choose_spec.1.1, ?_⟩
    have hχspec := (hbwd η hη).choose_spec
    have hfix : ∀ γ : Γ,
        bd ((γ : Γ) : PO n 1) ((hbwd η hη).choose) = (hbwd η hη).choose →
        bd (((f γ : Λ)) : PO n 1) η = η :=
      cuspStab_corr_rev hA hI hBb hG hΓ hΛ f hχspec.1.1 hη hχspec.1.2
    exact (hfwd _ hχspec.1.1).unique (hFspec _ hχspec.1.1) ⟨hη, hfix⟩

end

end Work.Mostow
