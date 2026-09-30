import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped Pointwise

/-- If `x` is an `M`-regular element in the maximal ideal of a Noetherian local ring `A` and `M`
is finitely generated, then every associated prime `p` of `M` lies in an associated prime `q` of
`M ⧸ xM` up to `x`: there is `q ∈ Ass(M ⧸ xM)` with `p + (x) ⊆ q`.

(State it in `namespace Work.BW`; only `Mathlib` is needed.)

Proof sketch. Take `N := (0 :_M p) = {m | ∀ a ∈ p, a • m = 0}`, a submodule of `M`. By
`isAssociatedPrime_iff` (Noetherian) `p = ann(x₀)` for some `x₀ ≠ 0`, so `N ∋ x₀` and `N ≠ 0`.
First `N ∩ xM = xN`: given `y ∈ N ∩ xM`, write `y = x • m`; for `a ∈ p`,
`x • (a • m) = a • (x • m) = a • y = 0`, hence `a • m = 0` because `IsSMulRegular M x`; so
`m ∈ N` and `y ∈ xN`. If `N = xN = Ideal.span {x} • N`, then Nakayama
(`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`, using `x ∈ m = (⊥ : Ideal A).jacobson`)
forces `N = ⊥`, contradiction. Hence there is `y ∈ N` with `y ∉ xM`, and the class
`ȳ ∈ M ⧸ xM` is nonzero and killed by `p` and by `x`. Apply
`exists_le_isAssociatedPrime_of_isNoetherianRing` to `ȳ` to get `q ∈ Ass(M ⧸ xM)` with
`(⊥ : Submodule A (M ⧸ xM)).colon {ȳ} ≤ q`; since `p ⊔ Ideal.span {x} ≤ ann(ȳ) = colon ⊥ {ȳ}`,
this is the desired `q`. -/
theorem ass_quot_reg {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A) (hxreg : IsSMulRegular M x)
    (p : Ideal A) (hp : p ∈ associatedPrimes A M) :
    ∃ q ∈ associatedPrimes A (QuotSMulTop x M), p ⊔ Ideal.span {x} ≤ q := by
  -- `p = ann x₀` for some `x₀ ≠ 0` (Noetherian case of the associated prime characterization).
  obtain ⟨hpprime, x₀, hx₀p⟩ := (isAssociatedPrime_iff (R := A) (M := M)).mp hp
  have hx₀mem : ∀ a ∈ p, a • x₀ = 0 := by
    intro a ha
    have : a ∈ (⊥ : Submodule A M).colon {x₀} := hx₀p ▸ ha
    simpa using this
  have hx₀ne : x₀ ≠ 0 := by
    rintro rfl
    rw [Submodule.colon_singleton_zero] at hx₀p
    exact hpprime.ne_top hx₀p
  -- The `p`-torsion submodule `N = (0 :_M p)`.
  let N : Submodule A M :=
    { carrier := {m | ∀ a ∈ p, a • m = 0}
      zero_mem' := by intro a _; simp
      add_mem' := by intro m n hm hn a ha; rw [smul_add, hm a ha, hn a ha, add_zero]
      smul_mem' := by intro r m hm a ha; rw [smul_comm, hm a ha, smul_zero] }
  have hNmem : ∀ m : M, m ∈ N ↔ ∀ a ∈ p, a • m = 0 := fun m => Iff.rfl
  have hx₀N : x₀ ∈ N := by rw [hNmem]; exact hx₀mem
  -- Nakayama: `N` cannot satisfy `N = span {x} • N`.
  have hjac : Ideal.span {x} ≤ (⊥ : Ideal A).jacobson :=
    le_trans ((Ideal.span_singleton_le_iff_mem _).mpr hx) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have key : ¬ (N ≤ Ideal.span {x} • N) := by
    intro hle
    have hbot : N = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) N
        (IsNoetherian.noetherian N) hle hjac
    refine hx₀ne ?_
    simpa [hbot] using hx₀N
  -- Hence `N ⊄ xM`, and regular multiplication by `x` gives `N ≤ xN` from `N ≤ xM`.
  have hnotle : ¬ (N ≤ x • (⊤ : Submodule A M)) := by
    intro h
    apply key
    rw [Submodule.ideal_span_singleton_smul]
    intro y hy
    have hy' : y ∈ x • (⊤ : Submodule A M) := h hy
    obtain ⟨b, _, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists y x ⊤).mp hy'
    refine (Submodule.mem_smul_pointwise_iff_exists y x N).mpr ⟨b, ?_, hb⟩
    rw [hNmem]
    intro a ha
    have h1 : a • y = 0 := (hNmem y).mp hy a ha
    have h2 : x • (a • b) = 0 := by rw [← smul_comm a x b, hb]; exact h1
    exact IsSMulRegular.right_eq_zero_of_smul hxreg h2
  obtain ⟨y, hyN, hyxM⟩ := SetLike.not_le_iff_exists.mp hnotle
  -- The class of `y` in `M ⧸ xM` is nonzero, hence lies under an associated prime `q`.
  let π : M →ₗ[A] (M ⧸ x • (⊤ : Submodule A M)) := Submodule.mkQ _
  have hπy_ne : π y ≠ 0 := by
    rw [Submodule.mkQ_apply]
    intro h
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact hyxM h
  obtain ⟨q, hq, hqle⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing A (π y) hπy_ne
  have hy_ann : ∀ a ∈ p, a • y = 0 := (hNmem y).mp hyN
  -- `p` kills the class of `y`, and so does `x`; the colon is contained in `q`.
  refine ⟨q, hq, sup_le ?_ ?_⟩
  · intro a ha
    apply hqle
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [show a • π y = π (a • y) from (π.map_smul a y).symm, hy_ann a ha, π.map_zero]
  · rw [Ideal.span_le]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    apply hqle
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [show x • π y = π (x • y) from (π.map_smul x y).symm]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_smul_pointwise_iff_exists (x • y) x ⊤).mpr ⟨y, trivial, rfl⟩

end Work.BW
