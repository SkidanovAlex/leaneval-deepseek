import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.star_Irr
import Submission.Work.Hering.AppVII.Extraspecial

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped MonoidAlgebra commutatorElement BigOperators

namespace Work.Hering.AppVII

/-!
# The faithful characters of an extraspecial group

Let `Q` be an extraspecial `q`-group of order `q ^ (2m+1)`, so that `Q` has class two,
`Z(Q) = [Q,Q]` has order the prime `q`, and `|Q : Z(Q)| = q ^ (2m)`.  The classical character
theory of such a group says that an irreducible complex character `ψ` which is nontrivial on the
centre has degree `q ^ m` and vanishes outside the centre:

    ψ 1 = q ^ m,   ψ x = 0  for x ∉ Z(Q).

This is the character-theoretic input of Part 2 of Peterfalvi's Appendix VII.

The proof is the standard one.

* Any central element of `Q` acts on the (irreducible, hence simple) module of `ψ` as a scalar;
  the scalars form a monoid homomorphism `lam : Z(Q) →* ℂ` (`centerScalarHom`, Schur's lemma for
  the centre).
* `hZ` says that `lam` is nontrivial, hence (as `|Z(Q)| = q` is prime) injective: `lam c ≠ 1` for
  every `c ≠ 1` in the centre.
* For `x ∉ Z(Q)` choose `a` with `a * x ≠ x * a`.  Then `c = ⁅x⁻¹, a⁻¹⁆ ∈ [Q,Q] ≤ Z(Q)` is
  nontrivial, and `ρ(a⁻¹ x a) = ρ(x) · ρ(c) = lam c • ρ(x)`.  Taking traces and using the
  cyclicity of the trace gives `χ(x) = lam c · χ(x)`, so `χ(x) = 0`
  (`vanishes_off_center`).
* The second orthogonality relation `∑_x ψ x · ψ x⁻¹ = |Q|` now reduces to a sum over the centre,
  where every term equals `ψ(1)²`; hence `|Q| = |Z(Q)| · ψ(1)² = q · ψ(1)²`, and with
  `|Q| = q ^ (2m+1)` this gives `ψ(1) = q ^ m` (`card_eq_center_mul_degreeSq` and
  `degreeSquare`).
-/

/-- **An arithmetic consequence of `|Q| = |Z(Q)| · ψ(1)²`.**  If `d² · q = q ^ (2m+1)` with
`q ≠ 0`, then `d = q ^ m`. -/
theorem degreeSquare {q m d : ℕ} (hq : q ≠ 0)
    (h : (q : ℂ) * (d : ℂ) ^ 2 = (q : ℂ) ^ (2 * m + 1)) :
    (d : ℂ) = (q : ℂ) ^ m := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hpow : (q : ℂ) ^ (2 * m + 1) = (q : ℂ) * ((q : ℂ) ^ m) ^ 2 := by
    have e1 : (q : ℂ) ^ (2 * m + 1) = (q : ℂ) ^ (2 * m) * (q : ℂ) := pow_succ _ _
    have e2 : ((q : ℂ) ^ m) ^ 2 = (q : ℂ) ^ (2 * m) := by
      rw [← pow_mul, show m * 2 = 2 * m from by ring]
    rw [e1, e2, mul_comm]
  rw [hpow] at h
  have h2 : (d : ℂ) ^ 2 = ((q : ℂ) ^ m) ^ 2 := mul_left_cancel₀ hqC h
  have h4 : ((d : ℂ) - (q : ℂ) ^ m) * ((d : ℂ) + (q : ℂ) ^ m) = 0 := by
    have h5 : ((d : ℂ) - (q : ℂ) ^ m) * ((d : ℂ) + (q : ℂ) ^ m)
        = (d : ℂ) ^ 2 - ((q : ℂ) ^ m) ^ 2 := by ring
    rw [h5]
    exact sub_eq_zero.mpr h2
  have hsum : (d : ℂ) + (q : ℂ) ^ m ≠ 0 := by
    rw [← Nat.cast_pow, ← Nat.cast_add, Nat.cast_ne_zero]
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    exact (Nat.lt_of_lt_of_le (pow_pos hqpos m) (Nat.le_add_left _ _)).ne'
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact sub_eq_zero.mp h5
  · exact absurd h5 hsum

/-- **Schur's lemma for the centre.** In an irreducible finite dimensional representation of a
group over an algebraically closed field, every central element acts as a scalar, and the
scalars assemble into a monoid homomorphism from the centre. -/
theorem centerScalarHom {k : Type*} [Field k] [IsAlgClosed k] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ lam : Subgroup.center G →* k,
      ∀ z : Subgroup.center G, ρ (z : G) = lam z • (1 : V →ₗ[k] V) := by
  classical
  have hsmul_inj : ∀ {c c' : k}, c • (1 : V →ₗ[k] V) = c' • (1 : V →ₗ[k] V) → c = c' := by
    intro c c' h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h2 : c • v = c' • v := by
      have hh := congrFun (congrArg DFunLike.coe h) v
      simpa using hh
    have h3 : (c - c') • v = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 hv
  have key : ∀ z : Subgroup.center G, ∃ c : k, ρ (z : G) = c • (1 : V →ₗ[k] V) := by
    intro z
    have hz : (z : G) ∈ Submonoid.center G := z.2
    obtain ⟨c, hc⟩ :=
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := ρ)).2 (Representation.IntertwiningMap.centralMul ρ (z : G) hz)
    refine ⟨c, ?_⟩
    apply LinearMap.ext
    intro v
    have hh := congrFun (congrArg DFunLike.coe hc) v
    rw [Representation.IntertwiningMap.algebraMap_apply,
        Representation.IntertwiningMap.smul_apply,
        Representation.IntertwiningMap.coe_one] at hh
    have hh' : c • v = (Representation.IntertwiningMap.centralMul ρ (z : G) hz) v := by
      simpa using hh
    have h1 : (c • (1 : V →ₗ[k] V)) v = c • v := by simp
    rw [h1, hh']
    rfl
  choose sc hsc using key
  refine ⟨{ toFun := sc, map_one' := ?_, map_mul' := ?_ }, fun z => hsc z⟩
  · apply hsmul_inj
    rw [← hsc (1 : Subgroup.center G)]
    simp
  · intro z w
    apply hsmul_inj
    rw [← hsc (z * w),
      show ((z * w : Subgroup.center G) : G) = (z : G) * (w : G) from rfl, map_mul, hsc z, hsc w]
    rw [smul_mul_assoc, one_mul, smul_smul]

/-- **The order relation.** If a function `ψ` on a finite group `Q` vanishes off the subgroup `Z`,
equals `d · lam` on `Z` for a monoid homomorphism `lam : Z →* ℂ`, and has `∑ ψ x · ψ x⁻¹ = |Q|`,
then `|Q| = |Z| · d²`. -/
theorem card_eq_center_mul_degreeSq {Q : Type*} [Group Q] [Fintype Q] (Z : Subgroup Q)
    {lam : Z →* ℂ} {d : ℕ} {ψ : Q → ℂ}
    (hvan : ∀ x : Q, x ∉ Z → ψ x = 0)
    (hcen : ∀ z : Z, ψ (z : Q) = lam z * (d : ℂ))
    (hnorm : ∑ x : Q, ψ x * ψ x⁻¹ = (Nat.card Q : ℂ)) :
    (Nat.card Q : ℂ) = (Nat.card Z : ℂ) * (d : ℂ) ^ 2 := by
  classical
  have hsplit : ∑ x : Q, ψ x * ψ x⁻¹ = ∑ z : Z, ψ (z : Q) * ψ ((z : Q)⁻¹) := by
    have h1 : ∑ x : Q, ψ x * ψ x⁻¹
        = ∑ x ∈ (Finset.univ.filter (fun x => x ∈ Z)), ψ x * ψ x⁻¹ :=
      (Finset.sum_subset (Finset.filter_subset _ _) (fun x _ hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hvan x hx, zero_mul])).symm
    rw [h1, Finset.sum_subtype (s := Finset.univ.filter (fun x => x ∈ Z))
      (p := fun x => x ∈ Z) (h := fun x => by simp)]
  rw [← hnorm, hsplit]
  have hterm : ∀ z : Z, ψ (z : Q) * ψ ((z : Q)⁻¹) = (d : ℂ) ^ 2 := by
    intro z
    have h1 : ψ ((z : Q)⁻¹) = lam z⁻¹ * (d : ℂ) := by
      rw [← Subgroup.coe_inv Z z, hcen z⁻¹]
    have h2 : lam z * lam z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [hcen z, h1]
    calc lam z * (d : ℂ) * (lam z⁻¹ * (d : ℂ))
        = (lam z * lam z⁻¹) * ((d : ℂ) * (d : ℂ)) := by ring
      _ = 1 * ((d : ℂ) * (d : ℂ)) := by rw [h2]
      _ = (d : ℂ) ^ 2 := by ring
  rw [Finset.sum_congr rfl (fun z _ => hterm z), Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, nsmul_eq_mul]

/-- **Vanishing off the centre.**  Let `Q` be a finite group whose centre has order the prime `q`
and whose derived subgroup is central, let `ρ` be an irreducible finite dimensional complex
representation of `Q` on which every central element acts by a scalar `lam z`, with `lam`
nontrivial.  Then the character of `ρ` vanishes outside the centre. -/
theorem vanishes_off_center {Q : Type*} [Group Q] [Fintype Q] {q : ℕ} (hq : q.Prime)
    (hZcard : Nat.card (Subgroup.center Q) = q)
    (hcomm : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Q V) [ρ.IsIrreducible]
    (lam : Subgroup.center Q →* ℂ)
    (hlam : ∀ z : Subgroup.center Q, ρ (z : Q) = lam z • (1 : V →ₗ[ℂ] V))
    (hlamnt : ∃ z₀ : Subgroup.center Q, lam z₀ ≠ 1) :
    ∀ x : Q, x ∉ Subgroup.center Q → ρ.character x = 0 := by
  classical
  have hker : MonoidHom.ker lam = ⊥ := by
    rcases hlamnt with ⟨z₀, hz₀⟩
    have hdvd : Nat.card (MonoidHom.ker lam) ∣ q := by
      rw [← hZcard]
      exact Subgroup.card_subgroup_dvd_card (MonoidHom.ker lam)
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · rwa [Subgroup.card_eq_one] at h1
    · exfalso
      have htop : MonoidHom.ker lam = ⊤ := by
        refine (Subgroup.card_eq_iff_eq_top (MonoidHom.ker lam)).mp ?_
        rw [h1, hZcard]
      exact hz₀ (MonoidHom.mem_ker.mp (by rw [htop]; exact Subgroup.mem_top z₀))
  intro x hx
  have hx' : ¬ ∀ g : Q, g * x = x * g := fun h => hx (Subgroup.mem_center_iff.mpr h)
  push_neg at hx'
  obtain ⟨a, ha⟩ := hx'
  set c : Q := ⁅x⁻¹, a⁻¹⁆ with hcdef
  have hcZ : c ∈ Subgroup.center Q :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top x⁻¹) (Subgroup.mem_top a⁻¹))
  have hcne : c ≠ 1 := by
    intro h
    apply ha
    have h2 : x⁻¹ * a⁻¹ = a⁻¹ * x⁻¹ :=
      commutatorElement_eq_one_iff_mul_comm.mp (hcdef ▸ h)
    have h3 : a * x = x * a := by
      have := congrArg Inv.inv h2
      simpa using this
    exact h3
  have hlamc : lam ⟨c, hcZ⟩ ≠ 1 := by
    intro h
    have hmem : (⟨c, hcZ⟩ : Subgroup.center Q) ∈ MonoidHom.ker lam := MonoidHom.mem_ker.mpr h
    rw [hker] at hmem
    exact hcne (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem))
  have hmap : ρ (a⁻¹ * x * a) = lam ⟨c, hcZ⟩ • ρ x := by
    have hcx : a⁻¹ * x * a = x * c := by rw [hcdef, commutatorElement_def]; group
    rw [hcx, map_mul, hlam ⟨c, hcZ⟩]
    ext v
    simp
  have htr : (LinearMap.trace ℂ V) (ρ x)
      = lam ⟨c, hcZ⟩ * (LinearMap.trace ℂ V) (ρ x) := by
    have h1 : (LinearMap.trace ℂ V) (ρ (a⁻¹ * x * a)) = (LinearMap.trace ℂ V) (ρ x) := by
      have h2 : ρ (a⁻¹ * x * a) = ρ a⁻¹ * ρ x * ρ a := by rw [map_mul, map_mul]
      rw [h2, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one,
        one_mul]
    have h3 : (LinearMap.trace ℂ V) (ρ (a⁻¹ * x * a))
        = lam ⟨c, hcZ⟩ * (LinearMap.trace ℂ V) (ρ x) := by
      rw [hmap, map_smul, smul_eq_mul]
    exact h1.symm.trans h3
  have hzero : (LinearMap.trace ℂ V) (ρ x) = 0 := by
    have hfac : (1 - lam ⟨c, hcZ⟩) * (LinearMap.trace ℂ V) (ρ x) = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr htr
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h).symm hlamc
    · exact h
  exact hzero

/-- Inside `Q`, the centre of the top subgroup is the centre of `Q`. -/
theorem centerIn_top_eq_center {Q : Type*} [Group Q] :
    Work.PGroup.centerIn (⊤ : Subgroup Q) = Subgroup.center Q := by
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro a
    rw [← hzy]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨a, trivial⟩)
  · intro hy
    refine ⟨⟨y, trivial⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro w
    exact Subtype.ext (Subgroup.mem_center_iff.mp hy (w : Q))

theorem extraspecial_char {Q : Type*} [Group Q] [Fintype Q] {q m : ℕ} (hq : q.Prime) (hQ : Work.PGroup.IsExtraspecial q (⊤ : Subgroup Q)) (hcard : Nat.card Q = q ^ (2 * m + 1)) {ψ : Q → ℂ} (hψ : ψ ∈ Work.CharCore.Irr Q) (hZ : ∃ z : Subgroup.center Q, ψ (z : Q) ≠ ψ 1) : ψ 1 = (q : ℂ) ^ m ∧ ∀ x : Q, x ∉ Subgroup.center Q → ψ x = 0 := by
  classical
  obtain ⟨N, hN, hNchar⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hψ
  haveI hsimple : IsSimpleModule (Work.CharCore.groupAlgebra Q) N :=
    Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN
  haveI hirr : (Work.CharCore.submoduleRep N).IsIrreducible :=
    Work.Clifford.submoduleRep_isIrreducible hN
  haveI hnt : Nontrivial ↥N := IsSimpleModule.nontrivial (Work.CharCore.groupAlgebra Q) N
  have hchar : (Work.CharCore.submoduleRep N).character = ψ := hNchar
  have hZcard : Nat.card (Subgroup.center Q) = q := by
    rw [← centerIn_top_eq_center]
    exact hQ.2.2
  have hcomm : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q := by
    rw [← centerIn_top_eq_center]
    exact le_of_eq (Work.PGroup.center_eq_commutator_of_isExtraspecial (⊤ : Subgroup Q) hQ).symm
  obtain ⟨lam, hlam⟩ := centerScalarHom (Work.CharCore.submoduleRep N)
  set d : ℕ := Module.finrank ℂ ↥N with hd
  have hψ1 : ψ 1 = (d : ℂ) := by
    rw [← hchar, Representation.char_one]
  have hcen : ∀ z : Subgroup.center Q, ψ (z : Q) = lam z * (d : ℂ) := by
    intro z
    rw [← hchar, Representation.character, hlam z]
    show (LinearMap.trace ℂ ↥N) (lam z • (1 : ↥N →ₗ[ℂ] ↥N)) = lam z * (d : ℂ)
    rw [map_smul, LinearMap.trace_one, smul_eq_mul]
  obtain ⟨z0, hz0⟩ := hZ
  have hlamnt : ∃ z₀ : Subgroup.center Q, lam z₀ ≠ 1 := by
    refine ⟨z0, ?_⟩
    intro h
    apply hz0
    rw [hcen z0, h, one_mul, hψ1]
  have hvan : ∀ x : Q, x ∉ Subgroup.center Q → (Work.CharCore.submoduleRep N).character x = 0 :=
    vanishes_off_center hq hZcard hcomm (Work.CharCore.submoduleRep N) lam hlam hlamnt
  have hvanψ : ∀ x : Q, x ∉ Subgroup.center Q → ψ x = 0 := by
    intro x hx
    rw [← hchar]
    exact hvan x hx
  have hcardQ_ne : (Nat.card Q : ℂ) ≠ 0 := by
    rw [hcard, Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hq.ne_zero)
  have hnorm : ∑ x : Q, ψ x * ψ x⁻¹ = (Nat.card Q : ℂ) := by
    have hcp : Work.Clifford.charPair ψ ψ = 1 := by
      rw [Work.Clifford.charPair_eq_ite_of_mem_Irr hψ hψ, if_pos rfl]
    rw [Work.Clifford.charPair_apply] at hcp
    have h2 : (Nat.card Q : ℂ) * ((Nat.card Q : ℂ)⁻¹ * (∑ x : Q, ψ x * ψ x⁻¹))
        = (Nat.card Q : ℂ) * 1 := by rw [hcp]
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hcardQ_ne, one_mul] at h2
    exact h2
  have hcard_eq : (Nat.card Q : ℂ)
      = (Nat.card (Subgroup.center Q) : ℂ) * (d : ℂ) ^ 2 :=
    card_eq_center_mul_degreeSq (Subgroup.center Q) hvanψ hcen hnorm
  have hfinal : (d : ℂ) = (q : ℂ) ^ m := by
    have h1 : (q : ℂ) * (d : ℂ) ^ 2 = (q : ℂ) ^ (2 * m + 1) := by
      have h := hcard_eq
      rw [hZcard, hcard, Nat.cast_pow] at h
      exact h.symm
    exact degreeSquare hq.ne_zero h1
  exact ⟨hψ1.trans hfinal, hvanψ⟩

end Work.Hering.AppVII
