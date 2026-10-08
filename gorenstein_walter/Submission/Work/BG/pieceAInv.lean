import Mathlib
import Submission.Work.BG.CharBridge
import Submission.OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit
import Submission.OddOrder.GroupTheory.RepresentationTheory.BrauerPermutationUnconditional

open OddOrder.RepresentationTheory

namespace Work.BG

/-- Complex conjugation of class functions commutes with conjugation by an ambient element:
`(conj θ)^u = conj (θ^u)`.  Pointwise both sides are `star (θ (u * h * u⁻¹))`. -/
private theorem ClassFunction.conjBy_conj {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (u : G) (θ : ClassFunction ↥K ℂ) :
    ClassFunction.conjBy (G := G) (H := K) u θ.conj =
      (ClassFunction.conjBy (G := G) (H := K) u θ).conj := by
  ext h
  simp only [ClassFunction.conjBy_apply, ClassFunction.conj_apply]

/-- The same at the level of bundled irreducible characters. -/
private theorem conjBy_conjPerm {G : Type*} [Group G] {K : Subgroup G} [K.Normal] [Finite ↥K]
    (u : G) (θ : IrreducibleCharacter ↥K) :
    IrreducibleCharacter.conjBy (G := G) (H := K) u (IrreducibleCharacter.conjPerm ↥K θ) =
      IrreducibleCharacter.conjPerm ↥K
        (IrreducibleCharacter.conjBy (G := G) (H := K) u θ) := by
  apply IrreducibleCharacter.ext
  change ClassFunction.conjBy (G := G) (H := K) u ((θ : ClassFunction ↥K ℂ).conj) =
    (ClassFunction.conjBy (G := G) (H := K) u (θ : ClassFunction ↥K ℂ)).conj
  exact ClassFunction.conjBy_conj u (θ : ClassFunction ↥K ℂ)

/-- If an automorphism `σ` of the finite group `U` of odd order inverts a normal subgroup `K`,
then every `σ`-invariant irreducible character of `U` is trivial on `K`.

Indeed `a|_{K}` is real-valued, so the set of its irreducible constituents is stable under
complex conjugation; by Clifford's theorem those constituents form a single `U`-conjugation
orbit, of odd cardinality `[U : I_U(θ)]`.  If `θ ≠ 1` were a constituent, then (a real
irreducible character of the odd-order group `K` is trivial) `θ̄ ≠ θ`, and Clifford gives
`u ∈ U` with `θ^u = θ̄`; then `u ∉ I_U(θ)` while `u² ∈ I_U(θ)`, so `u = (u²)^{m+1}` with
`orderOf u = 2m+1` would lie in `I_U(θ)` — contradicting that `U` has odd order. -/
theorem pieceAInv {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (K : Subgroup U) [K.Normal] (hoddU : Odd (Nat.card U))
    (σ : MulAut U) (hσ : ∀ k ∈ K, σ k = k⁻¹)
    (a : OddOrder.RepresentationTheory.ClassFunction U ℂ)
    (ha : OddOrder.RepresentationTheory.IsIrreducibleCharacter a)
    (hfix : ∀ u : U, a (σ u) = a u) :
    ∀ k ∈ K, a k = a 1 := by
  classical
  haveI hKfintype : Fintype ↥K := Fintype.ofFinite ↥K
  haveI hKinv : Invertible (Nat.card ↥K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hoddK : Odd (Nat.card ↥K) := Odd.of_dvd_nat hoddU (Subgroup.card_subgroup_dvd_card K)
  let χ : IrreducibleCharacter U := ⟨a, ha⟩
  -- (1) the restriction of `a` to `K` is real-valued
  have hreal : ClassFunction.IsReal (ClassFunction.restrict K a) := by
    rw [ClassFunction.IsReal.iff_forall]
    intro k
    rw [ClassFunction.restrict_apply]
    have h1 : a ((k : U)⁻¹) = star (a (k : U)) := irreducibleCharacter_apply_inv χ (k : U)
    have h3 : σ (k : U) = (k : U)⁻¹ := hσ (k : U) k.2
    rw [← h1, ← h3, hfix (k : U)]
  -- (2) every irreducible constituent of the restriction is trivial
  have hconst : ∀ θ : IrreducibleCharacter ↥K, IrreducibleCharacter.LiesOver K χ θ →
      θ = trivialIrreducibleCharacter ↥K := by
    intro θ hθ
    by_contra hne
    have hnonreal : ¬ ClassFunction.IsReal (θ : ClassFunction ↥K ℂ) :=
      not_isReal_of_ne_trivial_of_odd_card' (G := ↥K) hoddK hne
    have hpermne : IrreducibleCharacter.conjPerm ↥K θ ≠ θ := fun h =>
      hnonreal ((IrreducibleCharacter.conjPerm_eq_self_iff θ).mp h)
    -- the complex conjugate character is also a constituent
    have hinner : ClassFunction.inner (ClassFunction.restrict K a)
        ((IrreducibleCharacter.conjPerm ↥K θ : IrreducibleCharacter ↥K) :
          ClassFunction ↥K ℂ)
        = star (ClassFunction.inner (ClassFunction.restrict K a)
            (θ : ClassFunction ↥K ℂ)) := by
      change ClassFunction.inner (ClassFunction.restrict K a) (θ : ClassFunction ↥K ℂ).conj
        = star (ClassFunction.inner (ClassFunction.restrict K a)
            (θ : ClassFunction ↥K ℂ))
      calc ClassFunction.inner (ClassFunction.restrict K a) (θ : ClassFunction ↥K ℂ).conj
          = ClassFunction.inner (ClassFunction.restrict K a).conj
              (θ : ClassFunction ↥K ℂ).conj := by rw [hreal]
        _ = ClassFunction.inner (θ : ClassFunction ↥K ℂ)
              (ClassFunction.restrict K a) := ClassFunction.inner_conj_conj _ _
        _ = star (ClassFunction.inner (ClassFunction.restrict K a)
              (θ : ClassFunction ↥K ℂ)) := ClassFunction.inner_star_comm _ _
    have hθ' : IrreducibleCharacter.LiesOver K χ (IrreducibleCharacter.conjPerm ↥K θ) := by
      show ClassFunction.restrictionMultiplicity K (χ : ClassFunction U ℂ)
        ((IrreducibleCharacter.conjPerm ↥K θ : IrreducibleCharacter ↥K) :
          ClassFunction ↥K ℂ) ≠ 0
      rw [ClassFunction.restrictionMultiplicity_def, hinner]
      exact star_ne_zero.mpr hθ
    obtain ⟨u, hu⟩ :=
      IrreducibleCharacter.RestrictionConstituentsSingleOrbit.exists_conj (H := K)
        (restrictionConstituentsSingleOrbit_of_isIrreducible (H := K) χ) hθ hθ'
    have hune : IrreducibleCharacter.conjBy (G := U) (H := K) u θ ≠ θ := fun h =>
      hpermne (hu.symm.trans h)
    have hunot : u ∉ IrreducibleCharacter.inertia (G := U) (H := K) θ := by
      rw [IrreducibleCharacter.mem_inertia]
      exact hune
    have haux : IrreducibleCharacter.conjBy (G := U) (H := K) u
        (IrreducibleCharacter.conjBy (G := U) (H := K) u θ) = θ := by
      calc IrreducibleCharacter.conjBy (G := U) (H := K) u
            (IrreducibleCharacter.conjBy (G := U) (H := K) u θ)
          = IrreducibleCharacter.conjBy (G := U) (H := K) u
              (IrreducibleCharacter.conjPerm ↥K θ) := by rw [hu]
        _ = IrreducibleCharacter.conjPerm ↥K
              (IrreducibleCharacter.conjBy (G := U) (H := K) u θ) :=
              conjBy_conjPerm u θ
        _ = IrreducibleCharacter.conjPerm ↥K (IrreducibleCharacter.conjPerm ↥K θ) := by
              rw [hu]
        _ = θ := by
            apply IrreducibleCharacter.ext
            rw [IrreducibleCharacter.conjPerm_apply_coe,
              IrreducibleCharacter.conjPerm_apply_coe, ClassFunction.conj_conj]
    have hu2 : u ^ 2 ∈ IrreducibleCharacter.inertia (G := U) (H := K) θ := by
      rw [IrreducibleCharacter.mem_inertia, pow_two, IrreducibleCharacter.conjBy_mul]
      exact haux
    -- parity: `u ∉ I`, `u ^ 2 ∈ I` and `orderOf u` odd give `u ∈ I`
    have hoddord : Odd (orderOf u) := Odd.of_dvd_nat hoddU (orderOf_dvd_natCard u)
    obtain ⟨m, hm⟩ := hoddord
    have hpow : u = (u ^ 2) ^ (m + 1) := by
      have h1 : u ^ (2 * m + 1) = 1 := by
        rw [← hm]
        exact pow_orderOf_eq_one u
      have h2 : u ^ (2 * (m + 1)) = u := by
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, h1, one_mul]
      rw [← pow_mul]
      exact h2.symm
    have huin : u ∈ IrreducibleCharacter.inertia (G := U) (H := K) θ := by
      rw [hpow]
      exact Subgroup.pow_mem _ hu2 (m + 1)
    exact hunot huin
  -- (3) the restriction is a scalar multiple of the trivial class function
  let c : ℂ := ClassFunction.inner (ClassFunction.restrict K a)
    ((trivialIrreducibleCharacter ↥K : IrreducibleCharacter ↥K) : ClassFunction ↥K ℂ)
  have hzero : ∀ θ : IrreducibleCharacter ↥K, θ ≠ trivialIrreducibleCharacter ↥K →
      ClassFunction.inner (ClassFunction.restrict K a) (θ : ClassFunction ↥K ℂ) = 0 := by
    intro θ hθ
    by_contra hne
    exact hθ (hconst θ (by
      show ClassFunction.restrictionMultiplicity K (χ : ClassFunction U ℂ)
        (θ : ClassFunction ↥K ℂ) ≠ 0
      rw [ClassFunction.restrictionMultiplicity_def]
      exact hne))
  have hdiff : ClassFunction.restrict K a
      - c • ((trivialIrreducibleCharacter ↥K : IrreducibleCharacter ↥K) :
          ClassFunction ↥K ℂ) = 0 := by
    refine classFunction_eq_zero_of_orthogonal _ fun θ => ?_
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
      irreducibleCharacter_inner_eq_ite (trivialIrreducibleCharacter ↥K) θ]
    by_cases h : trivialIrreducibleCharacter ↥K = θ
    · rw [if_pos h, ← h, mul_one, sub_self]
    · rw [if_neg h, mul_zero, sub_zero]
      exact hzero θ (fun hh => h hh.symm)
  have hb : ClassFunction.restrict K a
      = c • ((trivialIrreducibleCharacter ↥K : IrreducibleCharacter ↥K) :
          ClassFunction ↥K ℂ) := sub_eq_zero.mp hdiff
  intro k hk
  have h1 : ClassFunction.restrict K a ⟨k, hk⟩ = c := by
    have h := congrArg (fun φ : ClassFunction ↥K ℂ => φ ⟨k, hk⟩) hb
    simpa [ClassFunction.smul_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply] using h
  have h2 : ClassFunction.restrict K a ⟨1, K.one_mem⟩ = c := by
    have h := congrArg (fun φ : ClassFunction ↥K ℂ => φ ⟨1, K.one_mem⟩) hb
    simpa [ClassFunction.smul_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply] using h
  simpa using h1.trans h2.symm

end Work.BG
