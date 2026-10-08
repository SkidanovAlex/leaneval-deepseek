import Mathlib
import Submission.Work.Hering.Wagner.Core

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The transvection pieces of Wagner's step 6 (Peterfalvi I §1, pp. 190-191)

Let `V` be a finite `𝔽₂`-space, `Gm ≤ GL(V)` doubly transitive on `V \ {0}`, `U ≤ V` a
3-dimensional subspace, `X ≤ U` a hyperplane of `U` and `a ∈ X` a nonzero vector.  The last
step of the proof of Wagner's proposition asserts:

> for every 2-dimensional `X ⊂ U` and every `a ∈ X \ {0}`, `Ḡ_U` contains one of the two
> transvections with hyperplane `X` and vector `≠ 0, a`.

where `Ḡ_U = inducedSub Gm U` is the subgroup of `GL(U)` induced by the setwise stabiliser
`N_{Gm}(U)`.

The file is self-contained: it re-proves, with clean dependencies only on Mathlib and the
(untainted) definitions of `Core.lean`, the chain of orbit-counting lemmas of Wagner's
argument (steps 1 -- 5 of Peterfalvi I §1, pp. 189-191), and then assembles step 6 on top.
-/

set_option autoImplicit false

namespace Work.Hering.Wagner

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-! ## Elementary facts about `𝔽₂`-modules -/

/-- In a module over `𝔽₂` every element is its own negative. -/
theorem neg_eq_self_zmod2_module {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    -x = x := by
  rw [← neg_one_smul (ZMod 2) x, show (-1 : ZMod 2) = 1 from by decide, one_smul]

/-- In a module over `𝔽₂` every element is `2`-torsion. -/
theorem add_self_eq_zero_zmod2_module {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from by decide, zero_smul]

/-- Over `𝔽₂`, two distinct nonzero vectors are linearly independent, so the sum of the two
lines they span is 2-dimensional. -/
theorem finrank_span_singleton_sup_eq_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] {x y : M} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    Module.finrank (ZMod 2) ↥((ZMod 2 ∙ x) ⊔ (ZMod 2 ∙ y)) = 2 := by
  haveI : Module.Finite (ZMod 2) ↥((ZMod 2 ∙ x) ⊔ (ZMod 2 ∙ y)) := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) ↥(ZMod 2 ∙ x) := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) ↥(ZMod 2 ∙ y) := Module.Finite.of_finite
  have h := Submodule.finrank_sup_add_finrank_inf_eq (ZMod 2 ∙ x) (ZMod 2 ∙ y)
  rw [finrank_span_singleton hx, finrank_span_singleton hy] at h
  have hinf : (ZMod 2 ∙ x) ⊓ (ZMod 2 ∙ y) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hzx, hzy⟩ := hz
    rw [Submodule.mem_span_singleton] at hzx hzy
    obtain ⟨α, hα⟩ := hzx
    obtain ⟨β, hβ⟩ := hzy
    by_cases hβ0 : β = 0
    · rw [← hβ, hβ0, zero_smul]
    · have hβ1 : β = 1 := zmod2_eq_one_of_ne_zero hβ0
      rw [hβ1, one_smul] at hβ
      by_cases hα0 : α = 0
      · rw [← hα, hα0, zero_smul]
      · have hα1 : α = 1 := zmod2_eq_one_of_ne_zero hα0
        rw [hα1, one_smul] at hα
        exact absurd (hβ.trans hα.symm) (Ne.symm hxy)
  rw [hinf] at h
  simp at h
  omega

/-! ## The duality between fixed points and fixed hyperplanes (Lemma 2 of Peterfalvi I §1) -/

/-- Over `𝔽₂`, two nonzero functionals with the same kernel are equal. -/
theorem dual_ker_eq_of_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {φ ψ : Module.Dual (ZMod 2) V} (hφ : φ ≠ 0) (hψ : ψ ≠ 0)
    (h : LinearMap.ker φ = LinearMap.ker ψ) : φ = ψ := by
  have hne : ∃ v, φ v ≠ 0 := by
    by_contra hc
    exact hφ (LinearMap.ext fun w => by
      by_contra hw
      exact hc ⟨w, hw⟩)
  obtain ⟨v, hv⟩ := hne
  have hv1 : φ v = 1 := zmod2_eq_one_of_ne_zero hv
  have hψv : ψ v ≠ 0 := by
    intro h0
    have : v ∈ LinearMap.ker ψ := LinearMap.mem_ker.mpr h0
    rw [← h] at this
    exact hv (LinearMap.mem_ker.mp this)
  have hψ1 : ψ v = 1 := zmod2_eq_one_of_ne_zero hψv
  apply LinearMap.ext
  intro w
  have h1 : w - φ w • v ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, map_sub, map_smul, hv1, smul_eq_mul, mul_one, sub_self]
  have h1' : w - φ w • v ∈ LinearMap.ker ψ := by rw [← h]; exact h1
  rw [LinearMap.mem_ker, map_sub, map_smul, hψ1, smul_eq_mul, mul_one] at h1'
  exact (sub_eq_zero.mp h1').symm

/-- Every hyperplane of a finite-dimensional `𝔽₂`-space is the kernel of a nonzero linear
functional. -/
theorem exists_dual_ker_eq_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (hV : 0 < Module.finrank (ZMod 2) V)
    (L : Submodule (ZMod 2) V)
    (hL : Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1) :
    ∃ φ : Module.Dual (ZMod 2) V, φ ≠ 0 ∧ LinearMap.ker φ = L := by
  have hdim : Module.finrank (ZMod 2) (V ⧸ L) = 1 := by
    have h := Submodule.finrank_quotient_add_finrank L
    omega
  let e : (V ⧸ L) ≃ₗ[ZMod 2] ZMod 2 :=
    LinearEquiv.ofFinrankEq (V ⧸ L) (ZMod 2) (by rw [hdim, Module.finrank_self])
  refine ⟨(e : (V ⧸ L) →ₗ[ZMod 2] ZMod 2).comp L.mkQ, ?_, ?_⟩
  · rintro hφ
    obtain ⟨x, hx⟩ : ∃ x : V, ((e : (V ⧸ L) →ₗ[ZMod 2] ZMod 2).comp L.mkQ) x = 1 := by
      obtain ⟨y, hy⟩ := e.surjective 1
      obtain ⟨x, rfl⟩ := L.mkQ_surjective y
      exact ⟨x, by rw [LinearMap.comp_apply]; exact hy⟩
    rw [hφ] at hx
    simp at hx
  · rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]

/-- The complement of a single point in a finite type has cardinality one less. -/
theorem natCard_subtype_ne_aux {α : Type*} [Finite α] (z : α) :
    Nat.card {x : α // x ≠ z} = Nat.card α - 1 := by
  classical
  letI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x => x = z), Fintype.card_subtype_eq z]

/-- The kernel of `f - 1` and of `f^* - 1` have the same dimension. -/
theorem finrank_ker_dualMap_sub_one_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] [Module.Finite (ZMod 2) V] (f : V →ₗ[ZMod 2] V) :
    Module.finrank (ZMod 2) (LinearMap.ker (f.dualMap - 1)) =
      Module.finrank (ZMod 2) (LinearMap.ker (f - 1)) := by
  have h1 : f.dualMap - 1 = (f - 1).dualMap := by
    ext φ x
    simp
  rw [h1]
  have hrg : Module.finrank (ZMod 2) (LinearMap.range (f - 1).dualMap)
      = Module.finrank (ZMod 2) (LinearMap.range (f - 1)) :=
    LinearMap.finrank_range_dualMap_eq_finrank_range (f - 1)
  have h2 := LinearMap.finrank_range_add_finrank_ker (f - 1).dualMap
  have h3 := LinearMap.finrank_range_add_finrank_ker (f - 1)
  rw [hrg, Subspace.dual_finrank_eq] at h2
  exact Nat.add_left_cancel (h2.trans h3.symm)

/-- The number of nonzero fixed vectors of a linear map. -/
theorem natCard_fixed_pts_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (f : V →ₗ[ZMod 2] V) :
    Nat.card {x : V // x ≠ 0 ∧ f x = x} = Nat.card (LinearMap.ker (f - 1)) - 1 := by
  have e : {x : V // x ≠ 0 ∧ f x = x} ≃ {x : ↥(LinearMap.ker (f - 1)) // x ≠ 0} :=
    { toFun := fun x => ⟨⟨x.1, by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
          exact x.2.2⟩, fun h => x.2.1 (congrArg Subtype.val h)⟩
      invFun := fun y => ⟨y.1.1, fun h => y.2 (Subtype.ext h), by
          have h := y.1.2
          rwa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext (Subtype.ext rfl) }
  rw [Nat.card_congr e, natCard_subtype_ne_aux (0 : ↥(LinearMap.ker (f - 1)))]

/-- **Lemma 2 (a) of Peterfalvi I §1.**  For a linear automorphism `t` of a finite
`𝔽₂`-space, the number of nonzero fixed vectors of `t` equals the number of `t`-invariant
hyperplanes. -/
theorem card_fixed_pts_eq_card_fixed_hyp_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (hV : 0 < Module.finrank (ZMod 2) V) (t : V ≃ₗ[ZMod 2] V) :
    Nat.card {x : V // x ≠ 0 ∧ t x = x} =
      Nat.card {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧
          L.map (t : V →ₗ[ZMod 2] V) = L} := by
  let F : V →ₗ[ZMod 2] V := t
  change Nat.card {x : V // x ≠ 0 ∧ F x = x} =
      Nat.card {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧ L.map F = L}
  haveI : Finite (Module.Dual (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  let kerMap : {φ : Module.Dual (ZMod 2) V // φ ≠ 0 ∧ F.dualMap φ = φ} →
      {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧ L.map F = L} :=
    fun φ => ⟨LinearMap.ker φ.1, by
      refine ⟨?_, ?_⟩
      · have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := φ.1) φ.2.1
        omega
      · have hcomp : φ.1 ∘ₗ F = φ.1 := by
          rw [← LinearMap.dualMap_apply' F φ.1]; exact φ.2.2
        have hle : (LinearMap.ker φ.1).map F ≤ LinearMap.ker φ.1 := by
          rw [Submodule.map_le_iff_le_comap, ← LinearMap.ker_comp, hcomp]
        exact Submodule.eq_of_le_of_finrank_eq hle (by rw [LinearEquiv.finrank_map_eq])⟩
  have hbij : Function.Bijective kerMap := by
    constructor
    · intro φ ψ h
      have hk : LinearMap.ker φ.1 = LinearMap.ker ψ.1 := by
        have := congrArg Subtype.val h; simpa using this
      exact Subtype.ext (dual_ker_eq_of_aux φ.2.1 ψ.2.1 hk)
    · intro L
      obtain ⟨φ, hφne, hker⟩ := exists_dual_ker_eq_aux hV L.1 L.2.1
      have hsurjF : Function.Surjective F := t.surjective
      have hneq : (φ ∘ₗ F) ≠ 0 := by
        intro h0
        refine hφne (LinearMap.dualMap_injective_of_surjective hsurjF ?_)
        rw [LinearMap.dualMap_apply', LinearMap.dualMap_apply', h0]
        simp
      have hle : LinearMap.ker φ ≤ LinearMap.ker (φ ∘ₗ F) := by
        intro x hx
        rw [LinearMap.ker_comp, Submodule.mem_comap]
        have hmap : F x ∈ L.1 := by
          rw [← L.2.2]
          exact Submodule.mem_map_of_mem (hker ▸ hx)
        rwa [hker]
      have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero (f := φ) hφne
      have h2 := Module.Dual.finrank_ker_add_one_of_ne_zero (f := φ ∘ₗ F) hneq
      have hfin : Module.finrank (ZMod 2) (LinearMap.ker φ) =
          Module.finrank (ZMod 2) (LinearMap.ker (φ ∘ₗ F)) := by omega
      have hkeq : LinearMap.ker φ = LinearMap.ker (φ ∘ₗ F) :=
        Submodule.eq_of_le_of_finrank_eq hle hfin
      have hcomp : φ ∘ₗ F = φ :=
        (dual_ker_eq_of_aux hφne hneq hkeq).symm
      have hfix : F.dualMap φ = φ := by
        rw [LinearMap.dualMap_apply', hcomp]
      refine ⟨⟨φ, hφne, hfix⟩, ?_⟩
      apply Subtype.ext
      simpa using hker
  have hA : Nat.card {x : V // x ≠ 0 ∧ F x = x} = Nat.card (LinearMap.ker (F - 1)) - 1 :=
    natCard_fixed_pts_aux F
  have hB : Nat.card {φ : Module.Dual (ZMod 2) V // φ ≠ 0 ∧ F.dualMap φ = φ} =
      Nat.card {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧ L.map F = L} :=
    Nat.card_congr (Equiv.ofBijective kerMap hbij)
  have hC : Nat.card {φ : Module.Dual (ZMod 2) V // φ ≠ 0 ∧ F.dualMap φ = φ} =
      Nat.card (LinearMap.ker (F.dualMap - 1)) - 1 := natCard_fixed_pts_aux F.dualMap
  have hD : Nat.card (LinearMap.ker (F.dualMap - 1)) = Nat.card (LinearMap.ker (F - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker (F.dualMap - 1))),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker (F - 1))),
      finrank_ker_dualMap_sub_one_aux F]
  rw [hA, ← hB, hC, hD]

/-- Over `𝔽₂` a one-dimensional subspace is spanned by each of its nonzero elements. -/
theorem eq_span_of_finrank_eq_one {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {P : Submodule (ZMod 2) W} (hP : Module.finrank (ZMod 2) P = 1) {x : W} (hx : x ∈ P)
    (hx0 : x ≠ 0) : P = ZMod 2 ∙ x :=
  (Submodule.eq_of_le_of_finrank_eq (Submodule.span_singleton_le_iff_mem x P |>.mpr hx)
    (by rw [finrank_span_singleton hx0, hP])).symm

/-- The `T`-invariant lines of a finite `𝔽₂`-space are the lines spanned by the nonzero fixed
vectors of the invertible `T`. -/
theorem inv_lines_eq_fixed_pts_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V ≃ₗ[ZMod 2] V) :
    Nat.card {P : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) P = 1 ∧ P.map (T : V →ₗ[ZMod 2] V) = P}
      = Nat.card {x : V // x ≠ 0 ∧ T x = x} := by
  let f : {x : V // x ≠ 0 ∧ T x = x} →
      {P : Submodule (ZMod 2) V // Module.finrank (ZMod 2) P = 1 ∧
        P.map (T : V →ₗ[ZMod 2] V) = P} :=
    fun x => ⟨ZMod 2 ∙ x.1,
      ⟨finrank_span_singleton x.2.1, by
        rw [Submodule.map_span, Set.image_singleton]
        rw [show (T : V →ₗ[ZMod 2] V) x.1 = x.1 from x.2.2]⟩⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h : ZMod 2 ∙ x.1 = ZMod 2 ∙ y.1 := congrArg Subtype.val hxy
    have hx : x.1 ∈ ZMod 2 ∙ y.1 := h ▸ Submodule.mem_span_singleton_self x.1
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨μ, hμ⟩ := hx
    by_cases hμ0 : μ = 0
    · rw [hμ0, zero_smul] at hμ
      exact absurd hμ.symm x.2.1
    · have hμ1 : μ = 1 := zmod2_eq_one_of_ne_zero hμ0
      rw [hμ1, one_smul] at hμ
      exact Subtype.ext hμ.symm
  have hsurj : Function.Surjective f := by
    intro P
    have hne : ∃ y : V, y ∈ P.1 ∧ y ≠ 0 := by
      have hbot : (⊥ : Submodule (ZMod 2) V) < P.1 := bot_lt_iff_ne_bot.mpr (by
        intro h
        have h1 := P.2.1
        rw [h] at h1
        simp at h1)
      obtain ⟨y, hyP, hybot⟩ := SetLike.exists_of_lt hbot
      exact ⟨y, hyP, by simpa using hybot⟩
    obtain ⟨y, hyP, hy0⟩ := hne
    have hPeq : P.1 = ZMod 2 ∙ y := eq_span_of_finrank_eq_one P.2.1 hyP hy0
    have hTy : T y = y := by
      have hmem : T y ∈ P.1 := by
        rw [← P.2.2]
        exact Submodule.mem_map_of_mem hyP
      rw [hPeq, Submodule.mem_span_singleton] at hmem
      obtain ⟨μ, hμ⟩ := hmem
      rcases zmod2_eq_zero_or_eq_one μ with h | h
      · rw [h, zero_smul] at hμ
        exact absurd hμ.symm (fun hh => hy0 (T.injective (by simpa using hh)))
      · rw [h, one_smul] at hμ
        exact hμ.symm
    exact ⟨⟨y, hy0, hTy⟩, Subtype.ext hPeq.symm⟩
  have h1 : Nat.card {x : V // x ≠ 0 ∧ T x = x}
      ≤ Nat.card {P : Submodule (ZMod 2) V // Module.finrank (ZMod 2) P = 1 ∧
        P.map (T : V →ₗ[ZMod 2] V) = P} := Nat.card_le_card_of_injective f hinj
  have h2 : Nat.card {P : Submodule (ZMod 2) V // Module.finrank (ZMod 2) P = 1 ∧
        P.map (T : V →ₗ[ZMod 2] V) = P}
      ≤ Nat.card {x : V // x ≠ 0 ∧ T x = x} := Nat.card_le_card_of_surjective f hsurj
  omega

/-- **Lemma 2 of Peterfalvi I §1**, in the form "invariant hyperplanes versus invariant lines". -/
theorem card_inv_hyp_eq_card_inv_line_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (T : V ≃ₗ[ZMod 2] V) :
    Nat.card {H : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) V ∧
          H.map (T : V →ₗ[ZMod 2] V) = H}
      = Nat.card {P : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) P = 1 ∧ P.map (T : V →ₗ[ZMod 2] V) = P} := by
  by_cases hV : 0 < Module.finrank (ZMod 2) V
  · have h1 : Nat.card {H : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) V ∧
          H.map (T : V →ₗ[ZMod 2] V) = H}
      = Nat.card {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧
          L.map (T : V →ₗ[ZMod 2] V) = L} :=
    Nat.card_congr
      { toFun := fun H => ⟨H.1, by
          obtain ⟨h1, h2⟩ := H.2
          exact ⟨by omega, h2⟩⟩
        invFun := fun L => ⟨L.1, by
          obtain ⟨h1, h2⟩ := L.2
          exact ⟨by omega, h2⟩⟩
        left_inv := fun H => Subtype.ext rfl
        right_inv := fun L => Subtype.ext rfl }
    exact h1.trans
      ((card_fixed_pts_eq_card_fixed_hyp_aux hV T).symm.trans (inv_lines_eq_fixed_pts_aux T).symm)
  · have hV0 : Module.finrank (ZMod 2) V = 0 := by omega
    have hA : Nat.card {H : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) V ∧
          H.map (T : V →ₗ[ZMod 2] V) = H} = 0 := by
      rw [Nat.card_eq_zero]
      exact Or.inl ⟨fun H => by have h := H.2.1; omega⟩
    have hB : Nat.card {P : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) P = 1 ∧ P.map (T : V →ₗ[ZMod 2] V) = P} = 0 := by
      rw [Nat.card_eq_zero]
      exact Or.inl ⟨fun P => by
        have h1 := P.2.1
        have h2 : Module.finrank (ZMod 2) P ≤ Module.finrank (ZMod 2) V :=
          Submodule.finrank_le P.1
        omega⟩
    rw [hA, hB]

/-- An invariant subspace of a quotient is exactly the quotient of an invariant subspace. -/
theorem map_eq_iff_mapQ_map_eq_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (X : Submodule (ZMod 2) V) (h : V ≃ₗ[ZMod 2] V)
    (T : (V ⧸ X) ≃ₗ[ZMod 2] (V ⧸ X)) (hT : ∀ x : V, T (X.mkQ x) = X.mkQ (h x))
    (Z : Submodule (ZMod 2) V) (hZ : X ≤ Z) :
    Z.map (h : V →ₗ[ZMod 2] V) = Z ↔
      (Z.map X.mkQ).map (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) = Z.map X.mkQ := by
  have hcomp : (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) ∘ₗ X.mkQ = X.mkQ ∘ₗ (h : V →ₗ[ZMod 2] V) := by
    ext x
    exact hT x
  constructor
  · intro hZh
    rw [← Submodule.map_comp, hcomp, Submodule.map_comp, hZh]
  · intro hZh
    have hle : Z.map (h : V →ₗ[ZMod 2] V) ≤ Z := by
      rw [Submodule.map_le_iff_le_comap]
      intro z hz
      have h1 : X.mkQ (h z) ∈ Z.map X.mkQ := by
        have hq : X.mkQ z ∈ Z.map X.mkQ := Submodule.mem_map_of_mem hz
        have h2 : T (X.mkQ z) ∈ (Z.map X.mkQ).map (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) :=
          Submodule.mem_map_of_mem hq
        rw [hZh] at h2
        rwa [hT z] at h2
      have h3 : Submodule.comap X.mkQ (Z.map X.mkQ) = Z := by
        rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hZ]
      rw [← h3]
      exact h1
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [LinearEquiv.finrank_map_eq])


/-- Rank–nullity for the quotient map `V → V ⧸ W`: if `W ≤ T` then
`finrank (T.map W.mkQ) + finrank W = finrank T`. -/
private theorem finrank_map_mkQ_add_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (W T : Submodule (ZMod 2) V) (hWT : W ≤ T) :
    Module.finrank (ZMod 2) (T.map W.mkQ) + Module.finrank (ZMod 2) W
      = Module.finrank (ZMod 2) T := by
  have hfin := LinearMap.finrank_range_add_finrank_ker ((W.mkQ).domRestrict T)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hfin
  rw [← hfin]; congr 1
  rw [← Submodule.finrank_map_subtype_eq T (Submodule.comap T.subtype W.mkQ.ker), Submodule.ker_mkQ,
      Submodule.map_comap_subtype, inf_eq_right.mpr hWT]

/-- **Step 4 of Peterfalvi I §1, per element**: for an automorphism `h` preserving a subspace
`X`, the number of `h`-invariant hyperplanes of `V` containing `X` equals the number of
`h`-invariant `(finrank X + 1)`-dimensional subspaces containing `X`. -/
theorem card_inv_hyp_above_eq_lines_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (X : Submodule (ZMod 2) V) (h : V ≃ₗ[ZMod 2] V)
    (hX : X.map (h : V →ₗ[ZMod 2] V) = X) :
    Nat.card {Z : Submodule (ZMod 2) V //
        X ≤ Z ∧ Module.finrank (ZMod 2) Z + 1 = Module.finrank (ZMod 2) V ∧
          Z.map (h : V →ₗ[ZMod 2] V) = Z}
      = Nat.card {Y : Submodule (ZMod 2) V //
        X ≤ Y ∧ Module.finrank (ZMod 2) Y = Module.finrank (ZMod 2) X + 1 ∧
          Y.map (h : V →ₗ[ZMod 2] V) = Y} := by
  classical
  haveI : Finite (V ⧸ X) := Finite.of_surjective X.mkQ (Submodule.mkQ_surjective X)
  have hle : X ≤ Submodule.comap (h : V →ₗ[ZMod 2] V) X :=
    Submodule.map_le_iff_le_comap.mp (le_of_eq hX)
  let T₀ : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X) := X.mapQ X (h : V →ₗ[ZMod 2] V) hle
  have hT₀ : ∀ x : V, T₀ (X.mkQ x) = X.mkQ (h x) := fun x => Submodule.mapQ_apply _ _ _ x
  have hsurj : Function.Surjective T₀ := by
    intro y
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective X y
    exact ⟨X.mkQ (h.symm v), by rw [hT₀]; simp⟩
  have hinj : Function.Injective T₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hsurj
  let T : (V ⧸ X) ≃ₗ[ZMod 2] (V ⧸ X) := LinearEquiv.ofBijective T₀ ⟨hinj, hsurj⟩
  have hT : ∀ x : V, T (X.mkQ x) = X.mkQ (h x) := by
    intro x; change T₀ (X.mkQ x) = X.mkQ (h x); exact hT₀ x
  have hfinW : Module.finrank (ZMod 2) (V ⧸ X) + Module.finrank (ZMod 2) X
      = Module.finrank (ZMod 2) V := Submodule.finrank_quotient_add_finrank X
  have hmap : ∀ H : Submodule (ZMod 2) (V ⧸ X),
      Submodule.map X.mkQ (Submodule.comap X.mkQ H) = H := fun H =>
    Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)
  have eA : {H : Submodule (ZMod 2) (V ⧸ X) //
        Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) (V ⧸ X) ∧
          H.map (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) = H} ≃
      {Z : Submodule (ZMod 2) V //
        X ≤ Z ∧ Module.finrank (ZMod 2) Z + 1 = Module.finrank (ZMod 2) V ∧
          Z.map (h : V →ₗ[ZMod 2] V) = Z} :=
    { toFun := fun H => ⟨Submodule.comap X.mkQ H.1, by
        refine ⟨Submodule.le_comap_mkQ X H.1, ?_, ?_⟩
        · have h1 := finrank_map_mkQ_add_aux X (Submodule.comap X.mkQ H.1)
            (Submodule.le_comap_mkQ X H.1)
          rw [hmap H.1] at h1
          omega
        · rw [map_eq_iff_mapQ_map_eq_aux X h T hT (Submodule.comap X.mkQ H.1)
            (Submodule.le_comap_mkQ X H.1)]
          rw [hmap H.1]
          exact H.2.2⟩
      invFun := fun Z => ⟨Z.1.map X.mkQ, by
        refine ⟨?_, ?_⟩
        · have h1 := finrank_map_mkQ_add_aux X Z.1 Z.2.1
          omega
        · rw [← map_eq_iff_mapQ_map_eq_aux X h T hT Z.1 Z.2.1]
          exact Z.2.2.2⟩
      left_inv := fun H => Subtype.ext (hmap H.1)
      right_inv := fun Z => Subtype.ext (by
        show Submodule.comap X.mkQ (Z.1.map X.mkQ) = Z.1
        rw [Submodule.comap_map_mkQ, sup_eq_right.mpr Z.2.1]) }
  have eB : {Y : Submodule (ZMod 2) V //
        X ≤ Y ∧ Module.finrank (ZMod 2) Y = Module.finrank (ZMod 2) X + 1 ∧
          Y.map (h : V →ₗ[ZMod 2] V) = Y} ≃
      {P : Submodule (ZMod 2) (V ⧸ X) //
        Module.finrank (ZMod 2) P = 1 ∧
          P.map (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) = P} :=
    { toFun := fun Y => ⟨Y.1.map X.mkQ, by
        refine ⟨?_, ?_⟩
        · have h1 := finrank_map_mkQ_add_aux X Y.1 Y.2.1
          omega
        · rw [← map_eq_iff_mapQ_map_eq_aux X h T hT Y.1 Y.2.1]
          exact Y.2.2.2⟩
      invFun := fun P => ⟨Submodule.comap X.mkQ P.1, by
        refine ⟨Submodule.le_comap_mkQ X P.1, ?_, ?_⟩
        · have h1 := finrank_map_mkQ_add_aux X (Submodule.comap X.mkQ P.1)
            (Submodule.le_comap_mkQ X P.1)
          rw [hmap P.1] at h1
          omega
        · rw [map_eq_iff_mapQ_map_eq_aux X h T hT (Submodule.comap X.mkQ P.1)
            (Submodule.le_comap_mkQ X P.1)]
          rw [hmap P.1]
          exact P.2.2⟩
      left_inv := fun Y => Subtype.ext (by
        show Submodule.comap X.mkQ (Y.1.map X.mkQ) = Y.1
        rw [Submodule.comap_map_mkQ, sup_eq_right.mpr Y.2.1])
      right_inv := fun P => Subtype.ext (hmap P.1) }
  rw [← Nat.card_congr eA, Nat.card_congr eB]
  exact card_inv_hyp_eq_card_inv_line_aux T

/-- **Lemma 2 (b) of Peterfalvi I §1.** The number of orbits of a subgroup of `GL(V)` on the
nonzero vectors equals its number of orbits on the hyperplanes. -/
theorem orbCount_pts_eq_orbCount_hyp_aux (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hV : 0 < Module.finrank (ZMod 2) V) :
    orbCount H (Pts V) Set.univ = orbCount H (Hyp V) Set.univ := by
  classical
  have hP := orbCount_mul_card H (S := (Set.univ : Set (Pts V))) (fun _ _ _ _ => Set.mem_univ _)
  have hH := orbCount_mul_card H (S := (Set.univ : Set (Hyp V))) (fun _ _ _ _ => Set.mem_univ _)
  have h1 : ∀ g : H, Nat.card (fixedSubtype H (Set.univ : Set (Pts V)) g) =
      Nat.card {x : V // x ≠ 0 ∧ (g : V ≃ₗ[ZMod 2] V) x = x} := fun g =>
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, by
          show (g : V ≃ₗ[ZMod 2] V) x.1.1 = x.1.1
          exact congrArg Subtype.val x.2.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ⟨Set.mem_univ _, by
          refine Subtype.ext ?_
          show (g : V ≃ₗ[ZMod 2] V) x.1 = x.1
          exact x.2.2⟩⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
  have h2 : ∀ g : H, Nat.card (fixedSubtype H (Set.univ : Set (Hyp V)) g) =
      Nat.card {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧
          L.map (g : V →ₗ[ZMod 2] V) = L} := fun g =>
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, by
          show x.1.1.map (g : V →ₗ[ZMod 2] V) = x.1.1
          exact congrArg Subtype.val x.2.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ⟨Set.mem_univ _, Subtype.ext (by
          show x.1.map (g : V →ₗ[ZMod 2] V) = x.1
          exact x.2.2)⟩⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
  have hsum : (∑ g : H, Nat.card (fixedSubtype H (Set.univ : Set (Pts V)) g)) =
      ∑ g : H, Nat.card (fixedSubtype H (Set.univ : Set (Hyp V)) g) := by
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [h1 g, h2 g]
    exact card_fixed_pts_eq_card_fixed_hyp_aux hV (g : V ≃ₗ[ZMod 2] V)
  rw [hP, hH] at hsum
  exact Nat.mul_right_cancel (natCard_pos_of_fintype H) hsum

theorem orbCount_stabPt_pts_aux (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm) {a : V}
    (ha : a ≠ 0) (hV : 2 ≤ Module.finrank (ZMod 2) V) :
    orbCount (stabPt Gm a) (Pts V) Set.univ = 2 := by
  classical
  obtain ⟨b, hb0, hba⟩ := exists_ne_zero_ne_of_finrank (V := V) hV ha
  have hfix : ∀ g ∈ stabPt Gm a, g • (⟨a, ha⟩ : Pts V) = ⟨a, ha⟩ := by
    intro g hg
    refine Subtype.ext ?_
    show (g : V ≃ₗ[ZMod 2] V) a = a
    exact (mem_stabPt.mp hg).2
  have hne : ({x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} : Set (Pts V)).Nonempty := by
    refine ⟨⟨b, hb0⟩, ?_⟩
    show (⟨b, hb0⟩ : Pts V) ≠ ⟨a, ha⟩
    intro h
    exact hba (congrArg Subtype.val h)
  have hcomp : orbCount (stabPt Gm a) (Pts V) {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} = 1 := by
    refine orbCount_eq_one_of_transitive (stabPt Gm a) hne ?_
    intro x hx y hy
    have hxa : x.1 ≠ a := fun h => hx (Subtype.ext h)
    have hya : y.1 ≠ a := fun h => hy (Subtype.ext h)
    obtain ⟨g, hg, hgxy⟩ := IsTwoTrans.stabPt_trans h2 ha x.2 y.2 hxa hya
    exact ⟨g, hg, Subtype.ext hgxy⟩
  have huniv : (Set.univ : Set (Pts V)) = {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} ∪ {⟨a, ha⟩} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
    tauto
  have hU : ∀ g ∈ stabPt Gm a, ∀ y ∈ {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} ∪ {⟨a, ha⟩},
      g • y ∈ {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} ∪ {⟨a, ha⟩} := by
    intro g hg y hy
    exact huniv ▸ Set.mem_univ (g • y)
  have hS : ∀ g ∈ stabPt Gm a, ∀ y ∈ {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)},
      g • y ∈ {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} := by
    intro g hg y hy
    exact fun h => hy (Subtype.ext (g.injective (by
      have h' : g y.1 = a := by
        have h2 := congrArg Subtype.val h
        rwa [Pts.smul_val] at h2
      rw [h', (mem_stabPt.mp hg).2])))
  rw [huniv, orbCount_eq_succ_of_union_singleton _ (by simp) hfix hS hU, hcomp]

/-- The point stabiliser has exactly two orbits on the hyperplanes (Lemma 2 of Peterfalvi I §1,
applied to `G_a`). -/
theorem orbCount_stabPt_hyp_aux (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm) {a : V}
    (ha : a ≠ 0) (hV : 2 ≤ Module.finrank (ZMod 2) V) :
    orbCount (stabPt Gm a) (Hyp V) Set.univ = 2 := by
  rw [← orbCount_pts_eq_orbCount_hyp_aux (stabPt Gm a) (by omega)]
  exact orbCount_stabPt_pts_aux Gm h2 ha hV

/-- **Step 1.** The point stabiliser of a nonzero vector is transitive on the hyperplanes not
containing it. -/
theorem stabPt_trans_hypNotMem_aux (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm) {a : V}
    (ha : a ≠ 0) (hV : 2 ≤ Module.finrank (ZMod 2) V) :
    ∀ H₁ ∈ hypNotMem a, ∀ H₂ ∈ hypNotMem a, ∃ g ∈ stabPt Gm a, g • H₁ = H₂ := by
  classical
  have htwo := orbCount_stabPt_hyp_aux Gm h2 ha hV
  have hSin_inv : ∀ g ∈ stabPt Gm a, ∀ H ∈ hypMem a, g • H ∈ hypMem a := by
    intro g hg H hH
    rw [mem_hypMem] at hH ⊢
    have hga : (g : V ≃ₗ[ZMod 2] V) a = a := (mem_stabPt.mp hg).2
    rw [hyp_smul_val g H, Submodule.mem_map]
    exact ⟨a, hH, hga⟩
  have hSout_inv : ∀ g ∈ stabPt Gm a, ∀ H ∈ hypNotMem a, g • H ∈ hypNotMem a := by
    intro g hg H hH
    rw [mem_hypNotMem] at hH ⊢
    have hga : (g : V ≃ₗ[ZMod 2] V) a = a := (mem_stabPt.mp hg).2
    intro hmem
    rw [hyp_smul_val g H, Submodule.mem_map] at hmem
    obtain ⟨x, hx, hxg⟩ := hmem
    refine hH ?_
    have hxa : x = a := g.injective (by simpa [hxg, hga])
    rw [← hxa]
    exact hx
  have huniv : (Set.univ : Set (Hyp V)) = hypMem a ∪ hypNotMem a := by
    ext H
    constructor
    · intro _
      rw [Set.mem_union, mem_hypMem, mem_hypNotMem]
      by_cases h : a ∈ H.1
      · exact Or.inl h
      · exact Or.inr h
    · intro _
      exact Set.mem_univ H
  have hdisj : Disjoint (hypMem a) (hypNotMem a) := by
    rw [Set.disjoint_left]
    intro H h1 h2
    rw [mem_hypMem] at h1
    rw [mem_hypNotMem] at h2
    exact h2 h1
  have hU : ∀ g ∈ stabPt Gm a, ∀ H ∈ hypMem a ∪ hypNotMem a,
      g • H ∈ hypMem a ∪ hypNotMem a := by
    intro g hg H hH
    have hUu : hypMem a ∪ hypNotMem a = (Set.univ : Set (Hyp V)) := huniv.symm
    rw [hUu]
    exact Set.mem_univ _
  have hsum : orbCount (stabPt Gm a) (Hyp V) (hypNotMem a) +
      orbCount (stabPt Gm a) (Hyp V) (hypMem a) = 2 := by
    rw [add_comm, ← orbCount_union _ hdisj hSin_inv hSout_inv hU, ← huniv, htwo]
  have hSin_ne : (hypMem a).Nonempty := by
    have hc := card_hypMem' (V := V) (a := a) ha (by omega)
    have hpos : 0 < Nat.card {H : Hyp V // H ∈ hypMem a} := by
      rw [hc]
      have h1 : 1 ≤ Module.finrank (ZMod 2) V - 1 := by omega
      have h2' : 2 ≤ 2 ^ (Module.finrank (ZMod 2) V - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (Module.finrank (ZMod 2) V - 1) := Nat.pow_le_pow_right (by norm_num) h1
      omega
    obtain ⟨hne, _⟩ := Nat.card_pos_iff.mp hpos
    obtain ⟨H⟩ := hne
    exact ⟨H.1, H.2⟩
  have hSout_ne : (hypNotMem a).Nonempty := by
    have hc := card_hypNotMem' (V := V) (a := a) ha
    have hpos : 0 < Nat.card {H : Hyp V // H ∈ hypNotMem a} := by
      rw [hc]; positivity
    obtain ⟨hne, _⟩ := Nat.card_pos_iff.mp hpos
    obtain ⟨H⟩ := hne
    exact ⟨H.1, H.2⟩
  have h1 := one_le_orbCount_of_nonempty (stabPt Gm a) hSout_ne
  have h2' := one_le_orbCount_of_nonempty (stabPt Gm a) hSin_ne
  have hout : orbCount (stabPt Gm a) (Hyp V) (hypNotMem a) = 1 := by omega
  exact transitive_of_orbCount_eq_one _ hout

theorem stabPt_inf_stabSub_trans_hypNotMem_aux (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm)
    {a : V} (ha : a ≠ 0) (hV : 2 ≤ Module.finrank (ZMod 2) V)
    (X : Submodule (ZMod 2) V) (hXle : Submodule.span (ZMod 2) ({a} : Set V) ≤ X)
    (hXf : Module.finrank (ZMod 2) X = 2) :
    ∀ H₁ ∈ hypNotMem a, ∀ H₂ ∈ hypNotMem a,
      ∃ g ∈ stabPt Gm a ⊓ stabSub X, g • H₁ = H₂ := by
  classical
  intro H₁ hH₁ H₂ hH₂
  letI : MulAction (stabPt Gm a) ↥(grassTwoMem a) :=
    mulActionSubtype _ _ (grassTwoMem_inv Gm ha)
  letI : MulAction (stabPt Gm a) ↥(hypNotMem a) :=
    mulActionSubtype _ _ (hypNotMem_inv Gm ha)
  have hA : ∀ Y Y' : ↥(grassTwoMem a), ∃ g : stabPt Gm a, g • Y = Y' := by
    intro Y Y'
    obtain ⟨g, hg, hgY⟩ := stabPt_trans_grassTwoMem Gm h2 ha Y.1 Y.2 Y'.1 Y'.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgY⟩
  have hB : ∀ H H' : ↥(hypNotMem a), ∃ g : stabPt Gm a, g • H = H' := by
    intro H H'
    obtain ⟨g, hg, hgH⟩ := stabPt_trans_hypNotMem_aux Gm h2 ha hV H.1 H.2 H'.1 H'.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgH⟩
  have hcop : Nat.Coprime (Nat.card ↥(grassTwoMem a)) (Nat.card ↥(hypNotMem a)) := by
    rw [card_grassTwoMem' ha, card_hypNotMem' ha]
    exact coprime_two_pow_sub_one _
  obtain ⟨g, hgX, hgH⟩ :=
    exists_smul_eq_of_smul_eq_of_coprime hA hB (⟨⟨X, hXf⟩, hXle⟩ : ↥(grassTwoMem a)) hcop
      ⟨H₁, hH₁⟩ ⟨H₂, hH₂⟩
  refine ⟨(g : V ≃ₗ[ZMod 2] V), ⟨g.2, ?_⟩, ?_⟩
  · have h1 : (g • (⟨X, hXf⟩ : Grass V 2)).1 = X :=
      congrArg Subtype.val (congrArg Subtype.val hgX)
    show X.map (g : V →ₗ[ZMod 2] V) = X
    exact h1
  · show (g : V ≃ₗ[ZMod 2] V) • H₁ = H₂
    exact congrArg Subtype.val hgH

theorem stabPt_stabPt_trans_hypMem_aux (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm)
    {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hV : 2 ≤ Module.finrank (ZMod 2) V) :
    ∀ H₁ ∈ {H : Hyp V | a ∈ H.1 ∧ b ∉ H.1}, ∀ H₂ ∈ {H : Hyp V | a ∈ H.1 ∧ b ∉ H.1},
      ∃ g ∈ stabPt (stabPt Gm a) b, g • H₁ = H₂ := by
  classical
  intro H₁ hH₁ H₂ hH₂
  obtain ⟨ha₁, hb₁⟩ := hH₁
  obtain ⟨ha₂, hb₂⟩ := hH₂
  let A : Submodule (ZMod 2) V := Submodule.span (ZMod 2) ({a} : Set V)
  let B : Submodule (ZMod 2) V := Submodule.span (ZMod 2) ({b} : Set V)
  let X : Submodule (ZMod 2) V := A ⊔ B
  have hAeq : A = Submodule.span (ZMod 2) ({a} : Set V) := rfl
  have hBeq : B = Submodule.span (ZMod 2) ({b} : Set V) := rfl
  have hXdef : X = A ⊔ B := rfl
  have hfA : Module.finrank (ZMod 2) A = 1 := by rw [hAeq]; exact finrank_span_singleton ha
  have hfB : Module.finrank (ZMod 2) B = 1 := by rw [hBeq]; exact finrank_span_singleton hb
  have hdisj : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [hAeq] at hx1
    rw [hBeq] at hx2
    change x ∈ Submodule.span (ZMod 2) ({a} : Set V) at hx1
    change x ∈ Submodule.span (ZMod 2) ({b} : Set V) at hx2
    rw [Submodule.mem_span_singleton] at hx1 hx2
    obtain ⟨c, hc⟩ := hx1
    obtain ⟨d, hd⟩ := hx2
    rcases eq_or_ne c 0 with hc0 | hc0
    · rw [hc0, zero_smul] at hc
      exact hc.symm
    · have hc1 : c = 1 := by
        have hv : c.val = 1 := by
          have hlt2 : c.val < 2 := ZMod.val_lt c
          rcases Nat.eq_zero_or_pos c.val with h0 | hpos
          · exact absurd ((ZMod.val_eq_zero c).mp h0) hc0
          · omega
        exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).mp hv
      rw [hc1, one_smul] at hc
      rcases eq_or_ne d 0 with hd0 | hd0
      · rw [hd0, zero_smul] at hd
        exact hd.symm
      · have hd1 : d = 1 := by
          have hv : d.val = 1 := by
            have hlt2 : d.val < 2 := ZMod.val_lt d
            rcases Nat.eq_zero_or_pos d.val with h0 | hpos
            · exact absurd ((ZMod.val_eq_zero d).mp h0) hd0
            · omega
          exact (ZMod.val_eq_one (by norm_num : 1 < 2) d).mp hv
        rw [hd1, one_smul] at hd
        exact absurd (hc.trans hd.symm) hab
  have hfX : Module.finrank (ZMod 2) X = 2 := by
    rw [hXdef]
    have h := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hfA, hfB, hdisj, finrank_bot] at h
    omega
  have hBle : B ≤ X := by rw [hXdef]; exact le_sup_right
  obtain ⟨g, hg, hgH⟩ := stabPt_inf_stabSub_trans_hypNotMem_aux Gm h2 hb hV X hBle hfX H₁ hb₁ H₂ hb₂
  obtain ⟨hgb, hgX⟩ := hg
  have hgb' : (g : V ≃ₗ[ZMod 2] V) b = b := (mem_stabPt.mp hgb).2
  -- `g a = a`
  have hga_mem_H₂ : (g : V ≃ₗ[ZMod 2] V) a ∈ H₂.1 := by
    have : g • H₁ = H₂ := hgH
    rw [← this, hyp_smul_val]
    exact Submodule.mem_map_of_mem ha₁
  have hga_mem_X : (g : V ≃ₗ[ZMod 2] V) a ∈ X := by
    have hmem : a ∈ X := by rw [hXdef]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)
    have hmap : (g : V ≃ₗ[ZMod 2] V) a ∈ X.map (g : V →ₗ[ZMod 2] V) :=
      Submodule.mem_map_of_mem hmem
    rwa [show X.map (g : V →ₗ[ZMod 2] V) = X from hgX] at hmap
  have hga_in_A : (g : V ≃ₗ[ZMod 2] V) a ∈ A :=
    mem_span_singleton_of_mem_sup_span ha ha₂ hb₂ hga_mem_H₂ (by
      rw [← hXdef]; exact hga_mem_X)
  have hga : (g : V ≃ₗ[ZMod 2] V) a = a := by
    rw [hAeq, Submodule.mem_span_singleton] at hga_in_A
    obtain ⟨α, hα⟩ := hga_in_A
    have hg0 : (g : V ≃ₗ[ZMod 2] V) a ≠ 0 := by
      intro h
      exact ha (g.injective (by rw [h]; simp))
    rcases eq_or_ne α 0 with hα0 | hα0
    · rw [hα0, zero_smul] at hα
      exact absurd hα.symm hg0
    · have hα1 : α = 1 := by
        have hv : α.val = 1 := by
          have hlt2 : α.val < 2 := ZMod.val_lt α
          rcases Nat.eq_zero_or_pos α.val with h0 | hpos
          · exact absurd ((ZMod.val_eq_zero α).mp h0) hα0
          · omega
        exact (ZMod.val_eq_one (by norm_num : 1 < 2) α).mp hv
      rw [hα1, one_smul] at hα
      exact hα.symm
  exact ⟨g, ⟨⟨hgb.1, MulAction.mem_stabilizer_iff.mpr (by simpa using hga)⟩,
    MulAction.mem_stabilizer_iff.mpr (by simpa using hgb')⟩, hgH⟩

/-! ## Elementary helpers -/

/-- `sp x` is the line spanned by `x`. -/
private def sp (x : V) : Submodule (ZMod 2) V := Submodule.span (ZMod 2) ({x} : Set V)

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  have h : x.val = 0 ∨ x.val = 1 := by omega
  rcases h with h | h
  · exact Or.inl ((ZMod.val_eq_zero x).mp h)
  · exact Or.inr ((ZMod.val_eq_one (by norm_num : 1 < 2) x).mp h)

private lemma sp_inf_sp_eq_bot {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    sp a ⊓ sp b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxa, hxb⟩ := hx
  change x ∈ Submodule.span (ZMod 2) ({a} : Set V) at hxa
  change x ∈ Submodule.span (ZMod 2) ({b} : Set V) at hxb
  rw [Submodule.mem_span_singleton] at hxa hxb
  obtain ⟨α, hα⟩ := hxa
  obtain ⟨β, hβ⟩ := hxb
  rw [Submodule.mem_bot]
  rcases zmod2_eq_zero_or_one α with hα0 | hα1
  · rw [hα0, zero_smul] at hα; exact hα.symm
  · rw [hα1, one_smul] at hα
    rcases zmod2_eq_zero_or_one β with hβ0 | hβ1
    · rw [hβ0, zero_smul] at hβ; exact absurd (hα.trans hβ.symm) ha
    · rw [hβ1, one_smul] at hβ; exact absurd (hα.trans hβ.symm) hab

private lemma sp_finrank {a : V} (ha : a ≠ 0) : Module.finrank (ZMod 2) (sp a) = 1 := by
  unfold sp
  exact finrank_span_singleton ha

private lemma sp_le_iff {a : V} {N : Submodule (ZMod 2) V} : sp a ≤ N ↔ a ∈ N := by
  unfold sp
  exact Submodule.span_singleton_le_iff_mem a N

/-- There is a hyperplane through `a` that does not contain `b`. -/
private lemma exists_hyp_mem_not_mem {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ W : Submodule (ZMod 2) V,
      Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V - 1 ∧ a ∈ W ∧ b ∉ W := by
  have hbA : b ∉ sp a := by
    intro h
    change b ∈ Submodule.span (ZMod 2) ({a} : Set V) at h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    rcases zmod2_eq_zero_or_one c with hc0 | hc1
    · rw [hc0, zero_smul] at hc; exact hb hc.symm
    · rw [hc1, one_smul] at hc; exact hab hc
  obtain ⟨f, hfb, hfmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem (p := sp a) hbA (inferInstance)
  have hfne : f ≠ 0 := fun h => hfb (by rw [h]; rfl)
  refine ⟨LinearMap.ker f, ?_, ?_, ?_⟩
  · have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := f) hfne
    omega
  · have hfa : f a = 0 := by
      have hmem : f a ∈ (sp a).map f :=
        Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self a)
      rw [hfmap] at hmem
      simpa using hmem
    rw [LinearMap.mem_ker]; exact hfa
  · rw [LinearMap.mem_ker]; exact hfb


/-! ## A finite surjection of equal cardinality is injective -/

private lemma injective_of_surjective_of_natCard {α β : Type*} [Finite α] [Finite β]
    {f : α → β} (hf : Function.Surjective f) (h : Nat.card α = Nat.card β) :
    Function.Injective f := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype β := Fintype.ofFinite β
  by_contra hne
  have hlt := Fintype.card_lt_of_surjective_not_injective f hf hne
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  omega


/-! ## Equivariant surjections with equal orbit counts are injective on fibres -/

private lemma orbit_eq_of_equivariant {G : Type*} [Group G] {α β : Type*}
    [MulAction G α] [MulAction G β] [Finite α] [Finite β]
    (H : Subgroup G) {S : Set α} {T : Set β} (f : α → β)
    (hfS : ∀ x ∈ S, f x ∈ T) (hf : ∀ g ∈ H, ∀ x ∈ S, f (g • x) = g • f x)
    (hsurj : ∀ y ∈ T, ∃ x ∈ S, f x = y) (hcard : orbCount H α S = orbCount H β T) :
    ∀ x ∈ S, ∀ y ∈ S, f x = f y → ∃ g ∈ H, g • x = y := by
  classical
  haveI hSfin : Finite ↥S := Finite.of_injective Subtype.val Subtype.coe_injective
  haveI hTfin : Finite ↥T := Finite.of_injective Subtype.val Subtype.coe_injective
  haveI hQfin : Finite (Quotient (orbitRelOn H S)) := Quotient.finite _
  haveI hQfin' : Finite (Quotient (orbitRelOn H T)) := Quotient.finite _
  let φ : ↥S → ↥T := fun x => ⟨f x.1, hfS x.1 x.2⟩
  have hφ : ∀ a b : ↥S, (orbitRelOn H S).r a b → (orbitRelOn H T).r (φ a) (φ b) := by
    intro u v huv
    obtain ⟨k, hk, hkuv⟩ := huv
    exact ⟨k, hk, by rw [← hf k hk u.1 u.2, hkuv]⟩
  let F : Quotient (orbitRelOn H S) → Quotient (orbitRelOn H T) := Quotient.map φ hφ
  have hFmk : ∀ x : ↥S, F (Quotient.mk _ x) = Quotient.mk _ (φ x) :=
    fun x => Quotient.map_mk φ hφ x
  have hFsurj : Function.Surjective F := by
    intro q
    obtain ⟨y, hy⟩ := Quotient.exists_rep q
    obtain ⟨x, hx, hxeq⟩ := hsurj y.1 y.2
    refine ⟨Quotient.mk _ ⟨x, hx⟩, ?_⟩
    rw [hFmk, ← hy]
    exact congrArg (Quotient.mk (orbitRelOn H T)) (Subtype.ext hxeq)
  have hcard' : Nat.card (Quotient (orbitRelOn H S)) = Nat.card (Quotient (orbitRelOn H T)) :=
    hcard
  have hinj : Function.Injective F := injective_of_surjective_of_natCard hFsurj hcard'
  intro x hx y hy hxy
  have h1 : F (Quotient.mk _ ⟨x, hx⟩) = F (Quotient.mk _ ⟨y, hy⟩) := by
    rw [hFmk, hFmk]
    exact congrArg (Quotient.mk (orbitRelOn H T)) (Subtype.ext hxy)
  have h2 := hinj h1
  have h3 := Quotient.exact h2
  obtain ⟨k, hk, hkxy⟩ := h3
  exact ⟨k, hk, hkxy⟩


/-! ## Translating `fixedSubtype` sets into `Submodule` subtypes -/

private def fixedSubtypeTwoEquiv (H : Subgroup (V ≃ₗ[ZMod 2] V)) (g : H)
    (A0 : Submodule (ZMod 2) V) (hfinA0 : Module.finrank (ZMod 2) A0 = 1) :
    fixedSubtype H {Y : Grass V 2 | A0 ≤ Y.1} g ≃
      {Y : Submodule (ZMod 2) V //
        A0 ≤ Y ∧ Module.finrank (ZMod 2) Y = Module.finrank (ZMod 2) A0 + 1 ∧
          Y.map (g : V →ₗ[ZMod 2] V) = Y} where
  toFun x := ⟨x.1.1, x.2.1, by have := x.1.2; omega, by
    have h := congrArg Subtype.val x.2.2
    rwa [Grass.smul_val] at h⟩
  invFun Y := ⟨⟨Y.1, by have := Y.2.2.1; omega⟩, Y.2.1, by
    apply Subtype.ext
    rw [Grass.smul_val]
    exact Y.2.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv Y := Subtype.ext rfl

private def fixedSubtypeHypEquiv (H : Subgroup (V ≃ₗ[ZMod 2] V)) (g : H)
    (X : Submodule (ZMod 2) V) (hV1 : 1 ≤ Module.finrank (ZMod 2) V) :
    fixedSubtype H {W : Hyp V | X ≤ W.1} g ≃
      {Z : Submodule (ZMod 2) V //
        X ≤ Z ∧ Module.finrank (ZMod 2) Z + 1 = Module.finrank (ZMod 2) V ∧
          Z.map (g : V →ₗ[ZMod 2] V) = Z} where
  toFun x := ⟨x.1.1, x.2.1, by have := x.1.2; omega, by
    have h := congrArg Subtype.val x.2.2
    rwa [Grass.smul_val] at h⟩
  invFun Z := ⟨⟨Z.1, by have := Z.2.2.1; omega⟩, Z.2.1, by
    apply Subtype.ext
    rw [Grass.smul_val]
    exact Z.2.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv Z := Subtype.ext rfl

private def fixedSubtypeThreeEquiv (H : Subgroup (V ≃ₗ[ZMod 2] V)) (g : H)
    (X : Submodule (ZMod 2) V) (hfinX : Module.finrank (ZMod 2) X = 2) :
    fixedSubtype H {Z : Grass V 3 | X ≤ Z.1} g ≃
      {Y : Submodule (ZMod 2) V //
        X ≤ Y ∧ Module.finrank (ZMod 2) Y = Module.finrank (ZMod 2) X + 1 ∧
          Y.map (g : V →ₗ[ZMod 2] V) = Y} where
  toFun x := ⟨x.1.1, x.2.1, by have := x.1.2; omega, by
    have h := congrArg Subtype.val x.2.2
    rwa [Grass.smul_val] at h⟩
  invFun Y := ⟨⟨Y.1, by have := Y.2.2.1; omega⟩, Y.2.1, by
    apply Subtype.ext
    rw [Grass.smul_val]
    exact Y.2.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv Y := Subtype.ext rfl


private lemma card_fixedSubtype_grassTwo_eq_hyp (H : Subgroup (V ≃ₗ[ZMod 2] V)) (g : H)
    {A0 : Submodule (ZMod 2) V} (hA0 : A0.map (g : V →ₗ[ZMod 2] V) = A0)
    (hfinA0 : Module.finrank (ZMod 2) A0 = 1) (hV1 : 1 ≤ Module.finrank (ZMod 2) V) :
    Nat.card (fixedSubtype H {Y : Grass V 2 | A0 ≤ Y.1} g)
      = Nat.card (fixedSubtype H {W : Hyp V | A0 ≤ W.1} g) := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  calc Nat.card (fixedSubtype H {Y : Grass V 2 | A0 ≤ Y.1} g)
      = Nat.card {Y : Submodule (ZMod 2) V // A0 ≤ Y ∧
          Module.finrank (ZMod 2) Y = Module.finrank (ZMod 2) A0 + 1 ∧
            Y.map (g : V →ₗ[ZMod 2] V) = Y} :=
        Nat.card_congr (fixedSubtypeTwoEquiv H g A0 hfinA0)
    _ = Nat.card {Z : Submodule (ZMod 2) V // A0 ≤ Z ∧
          Module.finrank (ZMod 2) Z + 1 = Module.finrank (ZMod 2) V ∧
            Z.map (g : V →ₗ[ZMod 2] V) = Z} :=
        (card_inv_hyp_above_eq_lines_aux A0 (g : V ≃ₗ[ZMod 2] V) hA0).symm
    _ = Nat.card (fixedSubtype H {W : Hyp V | A0 ≤ W.1} g) :=
        (Nat.card_congr (fixedSubtypeHypEquiv H g A0 hV1)).symm

private lemma card_fixedSubtype_grassThree_eq_hyp (H : Subgroup (V ≃ₗ[ZMod 2] V)) (g : H)
    {X : Submodule (ZMod 2) V} (hX : X.map (g : V →ₗ[ZMod 2] V) = X)
    (hfinX : Module.finrank (ZMod 2) X = 2) (hV1 : 1 ≤ Module.finrank (ZMod 2) V) :
    Nat.card (fixedSubtype H {Z : Grass V 3 | X ≤ Z.1} g)
      = Nat.card (fixedSubtype H {W : Hyp V | X ≤ W.1} g) := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  calc Nat.card (fixedSubtype H {Z : Grass V 3 | X ≤ Z.1} g)
      = Nat.card {Y : Submodule (ZMod 2) V // X ≤ Y ∧
          Module.finrank (ZMod 2) Y = Module.finrank (ZMod 2) X + 1 ∧
            Y.map (g : V →ₗ[ZMod 2] V) = Y} :=
        Nat.card_congr (fixedSubtypeThreeEquiv H g X hfinX)
    _ = Nat.card {Z : Submodule (ZMod 2) V // X ≤ Z ∧
          Module.finrank (ZMod 2) Z + 1 = Module.finrank (ZMod 2) V ∧
            Z.map (g : V →ₗ[ZMod 2] V) = Z} :=
        (card_inv_hyp_above_eq_lines_aux X (g : V ≃ₗ[ZMod 2] V) hX).symm
    _ = Nat.card (fixedSubtype H {W : Hyp V | X ≤ W.1} g) :=
        (Nat.card_congr (fixedSubtypeHypEquiv H g X hV1)).symm



private lemma orbCount_below_eq {Gm : Subgroup (V ≃ₗ[ZMod 2] V)} (h2 : IsTwoTrans Gm)
    {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hV : 2 ≤ Module.finrank (ZMod 2) V) :
    orbCount (stabPt (stabPt Gm a) b) (Grass V 2)
        {Y : Grass V 2 | sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b}
      = orbCount (stabPt (stabPt Gm a) b) (Grass V 3)
        {Z : Grass V 3 | sp a ⊔ sp b ≤ Z.1} := by
  classical
  set H : Subgroup (V ≃ₗ[ZMod 2] V) := stabPt (stabPt Gm a) b with hH
  have hfinA : Module.finrank (ZMod 2) (sp a) = 1 := sp_finrank ha
  have hfinB : Module.finrank (ZMod 2) (sp b) = 1 := sp_finrank hb
  have hdisj : sp a ⊓ sp b = ⊥ := sp_inf_sp_eq_bot ha hb hab
  have hfinX : Module.finrank (ZMod 2) (sp a ⊔ sp b : Submodule (ZMod 2) V) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (sp a) (sp b)
    rw [hfinA, hfinB, hdisj, finrank_bot] at h
    omega
  have hV1 : 1 ≤ Module.finrank (ZMod 2) V := by omega
  have ha_fix : ∀ g ∈ H, (g : V →ₗ[ZMod 2] V) a = a := by
    intro g hg
    rw [hH] at hg
    show (g : V ≃ₗ[ZMod 2] V) a = a
    exact (mem_stabPt.mp (mem_stabPt.mp hg).1).2
  have hb_fix : ∀ g ∈ H, (g : V →ₗ[ZMod 2] V) b = b := by
    intro g hg
    rw [hH] at hg
    show (g : V ≃ₗ[ZMod 2] V) b = b
    exact (mem_stabPt.mp hg).2
  have hmapA : ∀ g ∈ H, (sp a).map (g : V →ₗ[ZMod 2] V) = sp a := by
    intro g hg
    unfold sp
    rw [Submodule.map_span, Set.image_singleton, ha_fix g hg]
  have hmapB : ∀ g ∈ H, (sp b).map (g : V →ₗ[ZMod 2] V) = sp b := by
    intro g hg
    unfold sp
    rw [Submodule.map_span, Set.image_singleton, hb_fix g hg]
  have hmapX : ∀ g ∈ H, (sp a ⊔ sp b).map (g : V →ₗ[ZMod 2] V) = sp a ⊔ sp b := by
    intro g hg
    rw [Submodule.map_sup, hmapA g hg, hmapB g hg]
  -- invariance of the various sets
  have hAtil_inv : ∀ g ∈ H, ∀ Y ∈ {Y : Grass V 2 | sp a ≤ Y.1},
      g • Y ∈ {Y : Grass V 2 | sp a ≤ Y.1} := by
    intro g hg Y hY
    show sp a ≤ (g • Y).1
    rw [Grass.smul_val]
    exact le_of_eq_of_le (hmapA g hg).symm (Submodule.map_mono hY)
  have hA_inv : ∀ g ∈ H,
      ∀ Y ∈ {Y : Grass V 2 | sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b},
        g • Y ∈ {Y : Grass V 2 | sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b} := by
    intro g hg Y hY
    obtain ⟨hY1, hY2⟩ := hY
    refine ⟨?_, ?_⟩
    · show sp a ≤ (g • Y).1
      rw [Grass.smul_val]
      exact le_of_eq_of_le (hmapA g hg).symm (Submodule.map_mono hY1)
    · intro hcon
      apply hY2
      have hcon' : (g • Y).1 = sp a ⊔ sp b := hcon
      rw [Grass.smul_val] at hcon'
      have h2 : Y.1.map (g : V →ₗ[ZMod 2] V) = (sp a ⊔ sp b).map (g : V →ₗ[ZMod 2] V) := by
        rw [hcon', hmapX g hg]
      exact (Submodule.map_injective_of_injective (f := (g : V →ₗ[ZMod 2] V))
        (LinearEquiv.injective (g : V ≃ₗ[ZMod 2] V))) h2
  have hWa_inv : ∀ g ∈ H, ∀ W ∈ {W : Hyp V | sp a ≤ W.1}, g • W ∈ {W : Hyp V | sp a ≤ W.1} := by
    intro g hg W hW
    show sp a ≤ (g • W).1
    rw [Grass.smul_val]
    exact le_of_eq_of_le (hmapA g hg).symm (Submodule.map_mono hW)
  have hWX_inv : ∀ g ∈ H, ∀ W ∈ {W : Hyp V | sp a ⊔ sp b ≤ W.1},
      g • W ∈ {W : Hyp V | sp a ⊔ sp b ≤ W.1} := by
    intro g hg W hW
    show sp a ⊔ sp b ≤ (g • W).1
    rw [Grass.smul_val]
    exact le_of_eq_of_le (hmapX g hg).symm (Submodule.map_mono hW)
  have hB_inv : ∀ g ∈ H, ∀ Z ∈ {Z : Grass V 3 | sp a ⊔ sp b ≤ Z.1},
      g • Z ∈ {Z : Grass V 3 | sp a ⊔ sp b ≤ Z.1} := by
    intro g hg Z hZ
    show sp a ⊔ sp b ≤ (g • Z).1
    rw [Grass.smul_val]
    exact le_of_eq_of_le (hmapX g hg).symm (Submodule.map_mono hZ)
  -- (1d) : `{Y | sp a ≤ Y.1}` is `A` together with the single fixed point `X`
  have h1d : orbCount H (Grass V 2) {Y : Grass V 2 | sp a ≤ Y.1}
      = orbCount H (Grass V 2) {Y : Grass V 2 | sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b} + 1 := by
    have hx : (⟨sp a ⊔ sp b, hfinX⟩ : Grass V 2)
        ∉ {Y : Grass V 2 | sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b} := by
      simp
    have hfix : ∀ g ∈ H, g • (⟨sp a ⊔ sp b, hfinX⟩ : Grass V 2) = ⟨sp a ⊔ sp b, hfinX⟩ := by
      intro g hg
      apply Subtype.ext
      rw [Grass.smul_val]
      exact hmapX g hg
    have hset : {Y : Grass V 2 | sp a ≤ Y.1}
        = {Y : Grass V 2 | sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b}
            ∪ {(⟨sp a ⊔ sp b, hfinX⟩ : Grass V 2)} := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hY
        by_cases h : Y.1 = sp a ⊔ sp b
        · exact Or.inr (Subtype.ext h)
        · exact Or.inl ⟨hY, h⟩
      · rintro (⟨h1, _⟩ | h)
        · exact h1
        · rw [h]; exact le_sup_left
    have hU : ∀ g ∈ H,
        ∀ y ∈ {Y : Grass V 2 | sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b}
            ∪ {(⟨sp a ⊔ sp b, hfinX⟩ : Grass V 2)},
          g • y ∈ {Y : Grass V 2 | sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b}
            ∪ {(⟨sp a ⊔ sp b, hfinX⟩ : Grass V 2)} := by
      intro g hg y hy
      rcases hy with hy | hy
      · exact Or.inl (hA_inv g hg y hy)
      · rw [Set.mem_singleton_iff] at hy
        rw [hy, hfix g hg]
        exact Or.inr (Set.mem_singleton _)
    rw [hset]
    exact orbCount_eq_succ_of_union_singleton H hx hfix hA_inv hU
  -- (1a) : duality, `2`-spaces through `a` versus hyperplanes through `a`
  have h1a : orbCount H (Grass V 2) {Y : Grass V 2 | sp a ≤ Y.1}
      = orbCount H (Hyp V) {W : Hyp V | sp a ≤ W.1} := by
    have hb1 := orbCount_mul_card H (S := {Y : Grass V 2 | sp a ≤ Y.1}) hAtil_inv
    have hb2 := orbCount_mul_card H (S := {W : Hyp V | sp a ≤ W.1}) hWa_inv
    have hpt : ∀ g : H, Nat.card (fixedSubtype H {Y : Grass V 2 | sp a ≤ Y.1} g)
        = Nat.card (fixedSubtype H {W : Hyp V | sp a ≤ W.1} g) := by
      intro g
      exact card_fixedSubtype_grassTwo_eq_hyp H g (hmapA g g.2) hfinA hV1
    have hsum : orbCount H (Grass V 2) {Y : Grass V 2 | sp a ≤ Y.1} * Nat.card H
        = orbCount H (Hyp V) {W : Hyp V | sp a ≤ W.1} * Nat.card H := by
      rw [← hb1, ← hb2]
      exact Finset.sum_congr rfl (fun g _ => hpt g)
    exact Nat.mul_right_cancel (natCard_pos_of_fintype H) hsum
  -- (1b) : duality, `3`-spaces through `X` versus hyperplanes through `X`
  have h1b : orbCount H (Hyp V) {W : Hyp V | sp a ⊔ sp b ≤ W.1}
      = orbCount H (Grass V 3) {Z : Grass V 3 | sp a ⊔ sp b ≤ Z.1} := by
    have hb1 := orbCount_mul_card H (S := {W : Hyp V | sp a ⊔ sp b ≤ W.1}) hWX_inv
    have hb2 := orbCount_mul_card H (S := {Z : Grass V 3 | sp a ⊔ sp b ≤ Z.1}) hB_inv
    have hpt : ∀ g : H, Nat.card (fixedSubtype H {Z : Grass V 3 | sp a ⊔ sp b ≤ Z.1} g)
        = Nat.card (fixedSubtype H {W : Hyp V | sp a ⊔ sp b ≤ W.1} g) := by
      intro g
      exact card_fixedSubtype_grassThree_eq_hyp H g (hmapX g g.2) hfinX hV1
    have hsum : orbCount H (Hyp V) {W : Hyp V | sp a ⊔ sp b ≤ W.1} * Nat.card H
        = orbCount H (Grass V 3) {Z : Grass V 3 | sp a ⊔ sp b ≤ Z.1} * Nat.card H := by
      rw [← hb1, ← hb2]
      exact Finset.sum_congr rfl (fun g _ => (hpt g).symm)
    exact Nat.mul_right_cancel (natCard_pos_of_fintype H) hsum
  -- (1c) : hyperplanes through `a` = hyperplanes through `X` plus one further orbit
  have h1c : orbCount H (Hyp V) {W : Hyp V | sp a ≤ W.1}
      = orbCount H (Hyp V) {W : Hyp V | sp a ⊔ sp b ≤ W.1} + 1 := by
    have hWab_eq : {W : Hyp V | sp a ≤ W.1 ∧ ¬ (sp a ⊔ sp b ≤ W.1)}
        = {W : Hyp V | a ∈ W.1 ∧ b ∉ W.1} := by
      ext W
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(sp_le_iff.mp h1), fun hbW => h2 (sup_le h1 (sp_le_iff.mpr hbW))⟩
      · rintro ⟨h1, h2⟩
        exact ⟨sp_le_iff.mpr h1, fun hXW =>
          h2 (hXW (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b)))⟩
    have hWab_orb : orbCount H (Hyp V) {W : Hyp V | sp a ≤ W.1 ∧ ¬ (sp a ⊔ sp b ≤ W.1)} = 1 := by
      obtain ⟨W0, hW0fin, hW0a, hW0b⟩ := exists_hyp_mem_not_mem (V := V) ha hb hab
      have hW0mem : (⟨W0, hW0fin⟩ : Hyp V)
          ∈ {W : Hyp V | sp a ≤ W.1 ∧ ¬ (sp a ⊔ sp b ≤ W.1)} := by
        exact ⟨sp_le_iff.mpr hW0a, fun hXW =>
          hW0b (hXW (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b)))⟩
      refine orbCount_eq_one_of_transitive H ⟨(⟨W0, hW0fin⟩ : Hyp V), hW0mem⟩ ?_
      intro W1 hW1 W2 hW2
      rw [hWab_eq] at hW1 hW2
      obtain ⟨g, hg, hgW⟩ := stabPt_stabPt_trans_hypMem_aux Gm h2 ha hb hab hV W1 hW1 W2 hW2
      exact ⟨g, hg, hgW⟩
    have hWab_inv : ∀ g ∈ H,
        ∀ W ∈ {W : Hyp V | sp a ≤ W.1 ∧ ¬ (sp a ⊔ sp b ≤ W.1)},
          g • W ∈ {W : Hyp V | sp a ≤ W.1 ∧ ¬ (sp a ⊔ sp b ≤ W.1)} := by
      intro g hg W hW
      obtain ⟨h1, h2⟩ := hW
      refine ⟨hWa_inv g hg W h1, ?_⟩
      intro hcon
      apply h2
      intro x hx
      have hgx : g x ∈ sp a ⊔ sp b := by
        have hmem : g x ∈ (sp a ⊔ sp b).map (g : V →ₗ[ZMod 2] V) :=
          Submodule.mem_map_of_mem hx
        rwa [hmapX g hg] at hmem
      have hgxW : g x ∈ W.1.map (g : V →ₗ[ZMod 2] V) := by
        rw [← Grass.smul_val g W]
        exact hcon hgx
      obtain ⟨w, hw, hwg⟩ := hgxW
      have hwx : w = x := LinearEquiv.injective (g : V ≃ₗ[ZMod 2] V) hwg
      rwa [hwx] at hw
    have hunion : {W : Hyp V | sp a ≤ W.1}
        = {W : Hyp V | sp a ⊔ sp b ≤ W.1}
            ∪ {W : Hyp V | sp a ≤ W.1 ∧ ¬ (sp a ⊔ sp b ≤ W.1)} := by
      ext W
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro hW
        by_cases h : sp a ⊔ sp b ≤ W.1
        · exact Or.inl h
        · exact Or.inr ⟨hW, h⟩
      · rintro (h | ⟨h, _⟩)
        · exact le_trans le_sup_left h
        · exact h
    have hdisj : Disjoint {W : Hyp V | sp a ⊔ sp b ≤ W.1}
        {W : Hyp V | sp a ≤ W.1 ∧ ¬ (sp a ⊔ sp b ≤ W.1)} := by
      rw [Set.disjoint_left]
      intro W h1 h2
      exact h2.2 h1
    have hU : ∀ g ∈ H,
        ∀ W ∈ {W : Hyp V | sp a ⊔ sp b ≤ W.1}
            ∪ {W : Hyp V | sp a ≤ W.1 ∧ ¬ (sp a ⊔ sp b ≤ W.1)},
          g • W ∈ {W : Hyp V | sp a ⊔ sp b ≤ W.1}
            ∪ {W : Hyp V | sp a ≤ W.1 ∧ ¬ (sp a ⊔ sp b ≤ W.1)} := by
      intro g hg W hW
      rcases hW with hW | hW
      · exact Or.inl (hWX_inv g hg W hW)
      · exact Or.inr (hWab_inv g hg W hW)
    rw [hunion, orbCount_union H hdisj hWX_inv hWab_inv hU, hWab_orb]
  -- combine
  have e1 := h1d
  have e2 := h1a
  have e3 := h1c
  have e4 := h1b
  omega


/-! ## Step 5: the target -/

theorem trans_grassTwo_below_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Gm : Subgroup (V ≃ₗ[ZMod 2] V)} (h2 : IsTwoTrans Gm)
    {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hV : 2 ≤ Module.finrank (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hU : Module.finrank (ZMod 2) U = 3)
    (hXU : (Submodule.span (ZMod 2) ({a} : Set V)) ⊔ (Submodule.span (ZMod 2) ({b} : Set V)) ≤ U) :
    ∀ Y ∈ {Y : Grass V 2 | (Submodule.span (ZMod 2) ({a} : Set V)) ≤ Y.1 ∧
        Y.1 ≠ (Submodule.span (ZMod 2) ({a} : Set V)) ⊔ (Submodule.span (ZMod 2) ({b} : Set V)) ∧ Y.1 ≤ U},
      ∀ Y' ∈ {Y : Grass V 2 | (Submodule.span (ZMod 2) ({a} : Set V)) ≤ Y.1 ∧
        Y.1 ≠ (Submodule.span (ZMod 2) ({a} : Set V)) ⊔ (Submodule.span (ZMod 2) ({b} : Set V)) ∧ Y.1 ≤ U},
      ∃ g ∈ stabPt (stabPt Gm a) b ⊓ stabSub U, g • Y = Y' := by
  classical
  set H : Subgroup (V ≃ₗ[ZMod 2] V) := stabPt (stabPt Gm a) b with hH
  have hfinA : Module.finrank (ZMod 2) (sp a) = 1 := sp_finrank ha
  have hfinB : Module.finrank (ZMod 2) (sp b) = 1 := sp_finrank hb
  have hdisj : sp a ⊓ sp b = ⊥ := sp_inf_sp_eq_bot ha hb hab
  have hfinX : Module.finrank (ZMod 2) (sp a ⊔ sp b : Submodule (ZMod 2) V) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (sp a) (sp b)
    rw [hfinA, hfinB, hdisj, finrank_bot] at h
    omega
  have hV1 : 1 ≤ Module.finrank (ZMod 2) V := by omega
  have ha_fix : ∀ g ∈ H, (g : V →ₗ[ZMod 2] V) a = a := by
    intro g hg
    rw [hH] at hg
    show (g : V ≃ₗ[ZMod 2] V) a = a
    exact (mem_stabPt.mp (mem_stabPt.mp hg).1).2
  have hb_fix : ∀ g ∈ H, (g : V →ₗ[ZMod 2] V) b = b := by
    intro g hg
    rw [hH] at hg
    show (g : V ≃ₗ[ZMod 2] V) b = b
    exact (mem_stabPt.mp hg).2
  have hmapA : ∀ g ∈ H, (sp a).map (g : V →ₗ[ZMod 2] V) = sp a := by
    intro g hg
    unfold sp
    rw [Submodule.map_span, Set.image_singleton, ha_fix g hg]
  have hmapB : ∀ g ∈ H, (sp b).map (g : V →ₗ[ZMod 2] V) = sp b := by
    intro g hg
    unfold sp
    rw [Submodule.map_span, Set.image_singleton, hb_fix g hg]
  have hmapX : ∀ g ∈ H, (sp a ⊔ sp b).map (g : V →ₗ[ZMod 2] V) = sp a ⊔ sp b := by
    intro g hg
    rw [Submodule.map_sup, hmapA g hg, hmapB g hg]
  have hfinJoin : ∀ Y : Submodule (ZMod 2) V, Module.finrank (ZMod 2) Y = 2 → sp a ≤ Y →
      Y ≠ sp a ⊔ sp b →
      Module.finrank (ZMod 2) (Y ⊔ (sp a ⊔ sp b) : Submodule (ZMod 2) V) = 3 := by
    intro Y hfinY hY1 hY2
    have hle : sp a ≤ Y ⊓ (sp a ⊔ sp b) :=
      fun x hx => ⟨hY1 hx, Submodule.mem_sup_left hx⟩
    have h1le : 1 ≤ Module.finrank (ZMod 2) (Y ⊓ (sp a ⊔ sp b) : Submodule (ZMod 2) V) := by
      have hmono := Submodule.finrank_mono hle
      rw [hfinA] at hmono
      exact hmono
    have h2le : Module.finrank (ZMod 2) (Y ⊓ (sp a ⊔ sp b) : Submodule (ZMod 2) V) ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have hinf_le : Y ⊓ (sp a ⊔ sp b) ≤ Y := inf_le_left
      have hmono : Module.finrank (ZMod 2) (Y ⊓ (sp a ⊔ sp b) : Submodule (ZMod 2) V)
          ≤ Module.finrank (ZMod 2) Y := Submodule.finrank_mono hinf_le
      have heq : Y ⊓ (sp a ⊔ sp b) = Y := by
        refine Submodule.eq_of_le_of_finrank_eq hinf_le ?_
        omega
      have hYX : Y = sp a ⊔ sp b :=
        Submodule.eq_of_le_of_finrank_eq (heq ▸ inf_le_right) (by rw [hfinY, hfinX])
      exact hY2 hYX
    have hmain := Submodule.finrank_sup_add_finrank_inf_eq Y (sp a ⊔ sp b)
    omega
  -- the sets
  let A : Set (Grass V 2) := {Y : Grass V 2 | sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b}
  let B : Set (Grass V 3) := {Z : Grass V 3 | sp a ⊔ sp b ≤ Z.1}
  have hA_inv : ∀ g ∈ H, ∀ Y ∈ A, g • Y ∈ A := by
    intro g hg Y hY
    obtain ⟨hY1, hY2⟩ := hY
    refine ⟨?_, ?_⟩
    · show sp a ≤ (g • Y).1
      rw [Grass.smul_val]
      exact le_of_eq_of_le (hmapA g hg).symm (Submodule.map_mono hY1)
    · intro hcon
      apply hY2
      have hcon' : (g • Y).1 = sp a ⊔ sp b := hcon
      rw [Grass.smul_val] at hcon'
      have h2 : Y.1.map (g : V →ₗ[ZMod 2] V) = (sp a ⊔ sp b).map (g : V →ₗ[ZMod 2] V) := by
        rw [hcon', hmapX g hg]
      exact (Submodule.map_injective_of_injective (f := (g : V →ₗ[ZMod 2] V))
        (LinearEquiv.injective (g : V ≃ₗ[ZMod 2] V))) h2
  -- the join map
  let f : Grass V 2 → Grass V 3 := fun Y =>
    dite (sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b)
      (fun h => ⟨Y.1 ⊔ (sp a ⊔ sp b), hfinJoin Y.1 Y.2 h.1 h.2⟩)
      (fun _ => ⟨U, hU⟩)
  have hfval : ∀ (Y : Grass V 2) (h : sp a ≤ Y.1 ∧ Y.1 ≠ sp a ⊔ sp b),
      (f Y).1 = Y.1 ⊔ (sp a ⊔ sp b) :=
    fun Y h => congrArg Subtype.val (dif_pos h)
  have hfA : ∀ Y ∈ A, f Y ∈ B := by
    intro Y hY
    show sp a ⊔ sp b ≤ (f Y).1
    rw [hfval Y hY]
    exact le_sup_right
  have hf : ∀ g ∈ H, ∀ Y ∈ A, f (g • Y) = g • f Y := by
    intro g hg Y hY
    have hgY : sp a ≤ (g • Y).1 ∧ (g • Y).1 ≠ sp a ⊔ sp b := hA_inv g hg Y hY
    apply Subtype.ext
    rw [hfval (g • Y) hgY, Grass.smul_val g Y, Grass.smul_val g (f Y), hfval Y hY,
      Submodule.map_sup, hmapX g hg]
  have hsurj : ∀ Z ∈ B, ∃ Y ∈ A, f Y = Z := by
    intro Z hZ
    have hXZ : sp a ⊔ sp b ≤ Z.1 := hZ
    have hlt : sp a ⊔ sp b < Z.1 := by
      refine lt_of_le_of_ne hXZ ?_
      intro hcon
      have h3 : Module.finrank (ZMod 2) Z.1 = 3 := Z.2
      rw [← hcon, hfinX] at h3
      omega
    obtain ⟨c, hcZ, hcX⟩ := SetLike.exists_of_lt hlt
    have hc : c ∉ sp a := fun h => hcX (Submodule.mem_sup_left h)
    have hc0 : c ≠ 0 := fun h => hc (by rw [h]; exact Submodule.zero_mem _)
    have hac : a ≠ c := fun h => hc (by rw [← h]; exact Submodule.mem_span_singleton_self a)
    have hdisj_ac : sp a ⊓ sp c = ⊥ := sp_inf_sp_eq_bot ha hc0 hac
    have hfinAC : Module.finrank (ZMod 2) (sp a ⊔ sp c : Submodule (ZMod 2) V) = 2 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (sp a) (sp c)
      rw [hdisj_ac, finrank_bot, sp_finrank ha, sp_finrank hc0] at h
      omega
    have hdisj_cX : sp c ⊓ (sp a ⊔ sp b) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxc, hxX⟩ := hx
      rw [Submodule.mem_bot]
      by_contra hxne
      have hspan : sp x ≤ sp c := by rw [sp_le_iff]; exact hxc
      have hspan' : sp x ≤ sp a ⊔ sp b := by rw [sp_le_iff]; exact hxX
      have heq : sp x = sp c :=
        Submodule.eq_of_le_of_finrank_eq hspan (by rw [sp_finrank hxne, sp_finrank hc0])
      have : c ∈ sp a ⊔ sp b := by
        rw [heq] at hspan'
        exact hspan' (Submodule.mem_span_singleton_self c)
      exact hcX this
    have hfinCX : Module.finrank (ZMod 2) (sp c ⊔ (sp a ⊔ sp b) : Submodule (ZMod 2) V) = 3 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (sp c) (sp a ⊔ sp b)
      rw [hdisj_cX, finrank_bot, sp_finrank hc0, hfinX] at h
      omega
    have hsup : (sp a ⊔ sp c) ⊔ (sp a ⊔ sp b) = sp c ⊔ (sp a ⊔ sp b) := by
      refine le_antisymm ?_ ?_
      · refine sup_le (sup_le (le_trans le_sup_left le_sup_right) le_sup_left) le_sup_right
      · exact sup_le (le_trans le_sup_right le_sup_left) le_sup_right
    have hscZ : sp c ≤ Z.1 := by rw [sp_le_iff]; exact hcZ
    have hle1 : sp c ⊔ (sp a ⊔ sp b) ≤ Z.1 := sup_le hscZ hXZ
    have hfin1 : Module.finrank (ZMod 2) (sp c ⊔ (sp a ⊔ sp b) : Submodule (ZMod 2) V)
        = Module.finrank (ZMod 2) Z.1 := by rw [hfinCX, Z.2]
    refine ⟨⟨sp a ⊔ sp c, hfinAC⟩, ⟨le_sup_left, ?_⟩, ?_⟩
    · intro hcon
      exact hcX (hcon ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self c))
    · have hb : sp a ≤ (sp a ⊔ sp c) ∧ (sp a ⊔ sp c) ≠ sp a ⊔ sp b :=
        ⟨le_sup_left, fun hcon =>
          hcX (hcon ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self c))⟩
      apply Subtype.ext
      rw [hfval ⟨sp a ⊔ sp c, hfinAC⟩ hb]
      rw [hsup]
      exact Submodule.eq_of_le_of_finrank_eq hle1 hfin1
  -- the orbit-count equality from step 4
  have hcard' : orbCount H (Grass V 2) A = orbCount H (Grass V 3) B :=
    orbCount_below_eq h2 ha hb hab hV
  -- conclude
  intro Y hY Y' hY'
  obtain ⟨hY1, hY2, hYU⟩ := hY
  obtain ⟨hY'1, hY'2, hY'U⟩ := hY'
  have hYA : Y ∈ A := ⟨hY1, hY2⟩
  have hY'A : Y' ∈ A := ⟨hY'1, hY'2⟩
  have hjoinY : Y.1 ⊔ (sp a ⊔ sp b) = U := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hYU hXU) ?_
    rw [hfinJoin Y.1 Y.2 hY1 hY2, hU]
  have hjoinY' : Y'.1 ⊔ (sp a ⊔ sp b) = U := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hY'U hXU) ?_
    rw [hfinJoin Y'.1 Y'.2 hY'1 hY'2, hU]
  have hfeq : f Y = f Y' := by
    apply Subtype.ext
    rw [hfval Y ⟨hY1, hY2⟩, hfval Y' ⟨hY'1, hY'2⟩, hjoinY, hjoinY']
  obtain ⟨g, hgH, hgY⟩ :=
    orbit_eq_of_equivariant (S := A) (T := B) H f hfA hf hsurj hcard' Y hYA Y' hY'A hfeq
  have hgY1 : Y.1.map (g : V →ₗ[ZMod 2] V) = Y'.1 := by
    have := congrArg Subtype.val hgY
    rwa [Grass.smul_val] at this
  have hgSU : g ∈ stabSub U := by
    rw [mem_stabSub]
    calc U.map (g : V →ₗ[ZMod 2] V)
        = (Y.1 ⊔ (sp a ⊔ sp b)).map (g : V →ₗ[ZMod 2] V) := by rw [hjoinY]
      _ = Y.1.map (g : V →ₗ[ZMod 2] V) ⊔ (sp a ⊔ sp b).map (g : V →ₗ[ZMod 2] V) := by
            rw [Submodule.map_sup]
      _ = Y'.1 ⊔ (sp a ⊔ sp b) := by rw [hgY1, hmapX g hgH]
      _ = U := hjoinY'
  exact ⟨g, ⟨hgH, hgSU⟩, hgY⟩


/-- **Wagner's step 6 (Peterfalvi I §1, p. 191).**  For a 3-dimensional subspace `U`, a
hyperplane `X ≤ U` and a nonzero `a ∈ X`, the group induced on `U` by a doubly transitive
`Gm ≤ GL(V)` contains a transvection with hyperplane `X` and direction `≠ 0, a`. -/
theorem inducedSub_transvection_pieces {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Gm : Subgroup (V ≃ₗ[ZMod 2] V)} (h2 : IsTwoTrans Gm)
    (U : Submodule (ZMod 2) V) (hU : Module.finrank (ZMod 2) U = 3)
    (X : Submodule (ZMod 2) U) (hX : Module.finrank (ZMod 2) X + 1 = Module.finrank (ZMod 2) U)
    (a : U) (haX : a ∈ X) (ha0 : a ≠ 0) :
    ∃ τ ∈ inducedSub Gm U, (∀ x ∈ X, τ x = x) ∧
      ∃ c : U, c ∉ X ∧ ∃ w ∈ X, w ≠ 0 ∧ w ≠ a ∧ τ c = c + w := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hX2 : Module.finrank (ZMod 2) X = 2 := by omega
  -- ## Choosing a basis `a, b` of `X` and a complement `c`
  have hspanx_lt : (ZMod 2 ∙ a) < X := by
    refine lt_of_le_of_ne (Submodule.span_singleton_le_iff_mem a X |>.mpr haX) ?_
    intro heq
    have h1 : Module.finrank (ZMod 2) ↥(ZMod 2 ∙ a) = 1 := finrank_span_singleton ha0
    rw [heq, hX2] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨b, hbX, hbspan⟩ := SetLike.exists_of_lt hspanx_lt
  have hb0 : b ≠ 0 := fun h => hbspan (by rw [h]; exact Submodule.zero_mem _)
  have hba : b ≠ a := fun h => hbspan (by rw [h]; exact Submodule.mem_span_singleton_self a)
  have hXne_top : X ≠ ⊤ := by
    intro heq
    have h1 : Module.finrank (ZMod 2) X = Module.finrank (ZMod 2) U := by rw [heq]; simp
    omega
  obtain ⟨c, -, hcX⟩ := SetLike.exists_of_lt (lt_of_le_of_ne le_top hXne_top)
  have hXab : (ZMod 2 ∙ a) ⊔ (ZMod 2 ∙ b) = X := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · exact sup_le (Submodule.span_singleton_le_iff_mem a X |>.mpr haX)
        (Submodule.span_singleton_le_iff_mem b X |>.mpr hbX)
    · rw [finrank_span_singleton_sup_eq_two ha0 hb0 (Ne.symm hba), hX2]
  -- ## The same data inside `V`
  have coe_inj : ∀ x y : U, (x : V) = (y : V) → x = y := fun x y h => Subtype.ext h
  have haV : (a : V) ≠ 0 := fun h => ha0 (coe_inj a 0 (by simpa using h))
  have hbV : (b : V) ≠ 0 := fun h => hb0 (coe_inj b 0 (by simpa using h))
  have hbaV : (b : V) ≠ (a : V) := fun h => hba (coe_inj b a h)
  have hcV : (c : V) ≠ 0 := fun h => hcX (by rw [coe_inj c 0 (by simpa using h)]; exact X.zero_mem)
  have hacV : (a : V) ≠ (c : V) := fun h => hcX (by rw [coe_inj c a h.symm]; exact haX)
  have hV2 : 2 ≤ Module.finrank (ZMod 2) V := by
    have h := Submodule.finrank_le U
    omega
  have hXU : (ZMod 2 ∙ (a : V)) ⊔ (ZMod 2 ∙ (b : V)) ≤ U :=
    sup_le (Submodule.span_singleton_le_iff_mem (a : V) U |>.mpr a.2)
      (Submodule.span_singleton_le_iff_mem (b : V) U |>.mpr b.2)
  -- `c` is not in the plane `⟨a,b⟩`, and neither is `b + c`, nor is `b + c` equal to `a`
  have hcNotSup : (c : V) ∉ (ZMod 2 ∙ (a : V)) ⊔ (ZMod 2 ∙ (b : V)) := by
    intro hmem
    rw [Submodule.mem_sup] at hmem
    obtain ⟨p, hp, q, hq, hpq⟩ := hmem
    rw [Submodule.mem_span_singleton] at hp hq
    obtain ⟨α, rfl⟩ := hp
    obtain ⟨β, rfl⟩ := hq
    apply hcX
    have hcnj : c = α • a + β • b := Subtype.ext (by
      simpa only [Submodule.coe_add, Submodule.coe_smul] using hpq.symm)
    rw [hcnj]
    exact X.add_mem (X.smul_mem α haX) (X.smul_mem β hbX)
  have hcNotSpan : (c : V) ∉ ZMod 2 ∙ (a : V) := by
    intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨γ, hγ⟩ := hmem
    apply hcX
    have hcnj : c = γ • a := Subtype.ext (by
      rw [Submodule.coe_smul]
      exact hγ.symm)
    rw [hcnj]
    exact X.smul_mem γ haX
  have hbc0 : (b + c : U) ≠ 0 := by
    intro h
    apply hcX
    have h1 : c = b := by
      calc c = 0 + c := by rw [zero_add]
        _ = (b + b) + c := by rw [add_self_eq_zero_zmod2_module]
        _ = b + (b + c) := by rw [add_assoc]
        _ = b + 0 := by rw [h]
        _ = b := by rw [add_zero]
    rw [h1]
    exact hbX
  have hbca : (b + c : U) ≠ a := by
    intro h
    apply hcX
    have h1 : b + c = a := h
    have h2 : c = a + b := by
      calc c = 0 + c := by rw [zero_add]
        _ = (b + b) + c := by rw [add_self_eq_zero_zmod2_module]
        _ = b + (b + c) := by rw [add_assoc]
        _ = b + a := by rw [h1]
        _ = a + b := by rw [add_comm]
    rw [h2]
    exact X.add_mem haX hbX
  have hbcV : ((b + c : U) : V) ≠ 0 := fun h => hbc0 (coe_inj (b + c) 0 (by simpa using h))
  have habcV : (a : V) ≠ ((b + c : U) : V) := fun h => hbca (coe_inj (b + c) a h.symm)
  have hbcNotSup : ((b + c : U) : V) ∉ (ZMod 2 ∙ (a : V)) ⊔ (ZMod 2 ∙ (b : V)) := by
    intro hmem
    rw [Submodule.mem_sup] at hmem
    obtain ⟨p, hp, q, hq, hpq⟩ := hmem
    rw [Submodule.mem_span_singleton] at hp hq
    obtain ⟨α, rfl⟩ := hp
    obtain ⟨β, rfl⟩ := hq
    apply hcX
    have hbc_eq : b + c = α • a + β • b := coe_inj (b + c) (α • a + β • b) (by
      simpa only [Submodule.coe_add, Submodule.coe_smul] using hpq.symm)
    have hcnj : c = α • a + (β + 1) • b := by
      calc c = 0 + c := by rw [zero_add]
        _ = (b + b) + c := by rw [add_self_eq_zero_zmod2_module]
        _ = b + (b + c) := by rw [add_assoc]
        _ = b + (α • a + β • b) := by rw [hbc_eq]
        _ = α • a + (β + 1) • b := by
              rw [add_smul, one_smul]
              abel
    rw [hcnj]
    exact X.add_mem (X.smul_mem α haX) (X.smul_mem (β + 1) hbX)
  -- ## The two 2-spaces of `U` through `a`
  have hY1fin : Module.finrank (ZMod 2) ↥((ZMod 2 ∙ (a : V)) ⊔ (ZMod 2 ∙ (c : V))) = 2 :=
    finrank_span_singleton_sup_eq_two haV hcV hacV
  have hY2fin : Module.finrank (ZMod 2)
      ↥((ZMod 2 ∙ (a : V)) ⊔ (ZMod 2 ∙ ((b + c : U) : V))) = 2 :=
    finrank_span_singleton_sup_eq_two haV hbcV habcV
  let Y : Grass V 2 := ⟨(ZMod 2 ∙ (a : V)) ⊔ (ZMod 2 ∙ (c : V)), hY1fin⟩
  let Y' : Grass V 2 := ⟨(ZMod 2 ∙ (a : V)) ⊔ (ZMod 2 ∙ ((b + c : U) : V)), hY2fin⟩
  have hYmem : Y ∈ {Y : Grass V 2 | (ZMod 2 ∙ (a : V)) ≤ Y.1 ∧
      Y.1 ≠ (ZMod 2 ∙ (a : V)) ⊔ (ZMod 2 ∙ (b : V)) ∧ Y.1 ≤ U} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨le_sup_left, ?_, ?_⟩
    · intro heq
      apply hcNotSup
      rw [← heq]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self (c : V))
    · exact sup_le (Submodule.span_singleton_le_iff_mem (a : V) U |>.mpr a.2)
        (Submodule.span_singleton_le_iff_mem (c : V) U |>.mpr c.2)
  have hY'mem : Y' ∈ {Y : Grass V 2 | (ZMod 2 ∙ (a : V)) ≤ Y.1 ∧
      Y.1 ≠ (ZMod 2 ∙ (a : V)) ⊔ (ZMod 2 ∙ (b : V)) ∧ Y.1 ≤ U} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨le_sup_left, ?_, ?_⟩
    · intro heq
      apply hbcNotSup
      rw [← heq]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self ((b + c : U) : V))
    · exact sup_le (Submodule.span_singleton_le_iff_mem (a : V) U |>.mpr a.2)
        (Submodule.span_singleton_le_iff_mem ((b + c : U) : V) U |>.mpr (b + c).2)
  -- ## Step 5: an element of `G_{a,b}` moving `⟨a,c⟩` to `⟨a,b+c⟩`
  obtain ⟨g, hg, hgY⟩ :=
    trans_grassTwo_below_aux (Gm := Gm) h2 haV hbV (Ne.symm hbaV) hV2 U hU hXU Y hYmem Y' hY'mem
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgstab, hgUmem⟩ := hg
  rw [mem_stabPt] at hgstab
  obtain ⟨hgab, hgb⟩ := hgstab
  rw [mem_stabPt] at hgab
  obtain ⟨hgGm, hga⟩ := hgab
  have hgUmap : U.map (g : V →ₗ[ZMod 2] V) = U := mem_stabSub.mp hgUmem
  have hgUinvmap : U.map ((g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = U :=
    mem_stabSub.mp ((stabSub U).inv_mem hgUmem)
  have hmapU : ∀ x ∈ U, g x ∈ U := by
    intro x hx
    have h1 : x ∈ Submodule.comap (g : V →ₗ[ZMod 2] V) U :=
      Submodule.map_le_iff_le_comap.mp (le_of_eq hgUmap) hx
    simpa [Submodule.mem_comap] using h1
  have hmapUinv : ∀ x ∈ U, g⁻¹ x ∈ U := by
    intro x hx
    have h1 : x ∈ Submodule.comap ((g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) U :=
      Submodule.map_le_iff_le_comap.mp (le_of_eq hgUinvmap) hx
    simpa [Submodule.mem_comap] using h1
  -- ## The induced automorphism `τ` of `U`
  let gU : U →ₗ[ZMod 2] U :=
    { toFun := fun u => ⟨g (u : V), hmapU u u.2⟩
      map_add' := by intro x y; ext; simp [map_add]
      map_smul' := by intro r x; ext; simp }
  have hinj : Function.Injective gU := fun x y hxy =>
    Subtype.ext (g.injective (by
      have h := congrArg (fun z : U => (z : V)) hxy
      simpa [gU] using h))
  have hsurj : Function.Surjective gU := by
    intro y
    refine ⟨⟨g⁻¹ (y : V), hmapUinv y y.2⟩, ?_⟩
    ext
    simp [gU]
  let τ : U ≃ₗ[ZMod 2] U := LinearEquiv.ofBijective gU ⟨hinj, hsurj⟩
  have hτcoe : ∀ u : U, (τ u : V) = g (u : V) := fun u => rfl
  have hτa : τ a = a := Subtype.ext (by rw [hτcoe a]; exact hga)
  have hτb : τ b = b := Subtype.ext (by rw [hτcoe b]; exact hgb)
  refine ⟨τ, ?_, ?_, c, hcX, ?_⟩
  · exact mem_inducedSub.mpr ⟨g, hgGm, fun u => (hτcoe u).symm⟩
  · intro x hx
    rw [← hXab] at hx
    rw [Submodule.mem_sup] at hx
    obtain ⟨p, hp, q, hq, hpq⟩ := hx
    rw [Submodule.mem_span_singleton] at hp hq
    obtain ⟨α, rfl⟩ := hp
    obtain ⟨β, rfl⟩ := hq
    rw [← hpq, map_add, map_smul, map_smul, hτa, hτb]
  -- ## Reading off the transvection direction
  · have hgc_mem : g (c : V) ∈ Y'.1 := by
      have hYeq : Y'.1 = Y.1.map (g : V →ₗ[ZMod 2] V) := by
        have h1 : (g • Y).1 = Y'.1 := congrArg Subtype.val hgY
        rw [Grass.smul_val] at h1
        exact h1.symm
      rw [hYeq]
      exact Submodule.mem_map_of_mem
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self (c : V)))
    have hgc_not : g (c : V) ∉ ZMod 2 ∙ (a : V) := by
      intro hmem
      apply hcNotSpan
      rw [Submodule.mem_span_singleton] at hmem ⊢
      obtain ⟨γ, hγ⟩ := hmem
      have h2a : g.symm (a : V) = (a : V) :=
        g.injective (by rw [LinearEquiv.apply_symm_apply, hga])
      refine ⟨γ, ?_⟩
      have h1 : g.symm (γ • (a : V)) = g.symm (g (c : V)) :=
        congrArg (fun z => g.symm z) hγ
      rw [map_smul, LinearEquiv.symm_apply_apply, h2a] at h1
      exact h1
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hgc_mem
    rw [Submodule.mem_span_singleton] at hp hq
    obtain ⟨α, rfl⟩ := hp
    obtain ⟨β, rfl⟩ := hq
    have hβ1 : β = 1 := by
      rcases zmod2_eq_zero_or_eq_one β with h | h
      · exfalso
        apply hgc_not
        rw [← hpq, h, zero_smul, add_zero]
        exact Submodule.mem_span_singleton.mpr ⟨α, rfl⟩
      · exact h
    rw [hβ1, one_smul] at hpq
    have hgc : g (c : V) = (((α • a + b) + c : U) : V) := by
      rw [← hpq]
      simp only [Submodule.coe_add, Submodule.coe_smul]
      abel
    have hτc : τ c = c + (α • a + b) := by
      refine Subtype.ext ?_
      rw [hτcoe c, hgc]
      simp only [Submodule.coe_add]
      rw [add_comm]
    refine ⟨α • a + b, ?_, ?_, ?_, hτc⟩
    · exact X.add_mem (X.smul_mem α haX) hbX
    · intro h0
      have h1 : α • a + b = 0 := h0
      rcases zmod2_eq_zero_or_eq_one α with hα | hα
      · rw [hα, zero_smul, zero_add] at h1
        exact hb0 h1
      · rw [hα, one_smul] at h1
        have h2 : b = a := by
          calc b = 0 + b := by rw [zero_add]
            _ = (a + a) + b := by rw [add_self_eq_zero_zmod2_module]
            _ = a + (a + b) := by rw [add_assoc]
            _ = a + 0 := by rw [h1]
            _ = a := by rw [add_zero]
        exact hba h2
    · intro h0
      have h1 : α • a + b = a := h0
      rcases zmod2_eq_zero_or_eq_one α with hα | hα
      · rw [hα, zero_smul, zero_add] at h1
        exact hba h1
      · rw [hα, one_smul] at h1
        have h1' : a + b = a + (0 : U) := by rw [add_zero]; exact h1
        exact hb0 (add_left_cancel h1')

end Work.Hering.Wagner
