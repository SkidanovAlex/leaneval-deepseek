import Mathlib
import Submission.Work.BW.BWGradedBase
import Submission.Work.BW.rank_one_cut_length

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped Pointwise

/-- **Cut by `P` on a rank-one module: exact value of the length.**

Let `B` be a commutative ring, `𝔭 ≤ B` an ideal, `P ∈ B`, `M` a `B`-module annihilated by `𝔭`, and
`m₀ ∈ M`. Assume

* `𝔭` annihilates `M` (`hann`) — so `M` is a module over `A := B ⧸ 𝔭`,
* `P` is a non-zero-divisor on `M` (`hP`),
* the annihilator of `m₀` is exactly `𝔭` (`hx`) — equivalently `B·m₀ ≅ A`,
* `M ⧸ B·m₀` has finite length (`hfin`) — the "rank one" condition.

Then cutting `M` by `P` has exactly the length of cutting `B` by `𝔭 + (P)`:
`ℓ_B(M ⧸ P·M) = ℓ_B(B ⧸ (𝔭 + (P)))`.

Route. Put `N := B·m₀` and `T := M ⧸ N` (`T` of finite length by `hfin`). The map `B → N`,
`b ↦ b·m₀` is onto with kernel `𝔭` (`hann`, `hx`), so `N ≅ B ⧸ 𝔭` and `N ⧸ P·N ≅ B ⧸ (𝔭 + (P))`.
Length additivity in `0 → N/(N ∩ P·M) → M/P·M → M/(N + P·M) → 0` gives
`ℓ(M/P·M) = ℓ(N/(N ∩ P·M)) + ℓ(T/P·T)`, and in `0 → (N ∩ P·M)/P·N → N/P·N → N/(N ∩ P·M) → 0`
gives `ℓ(N/(N∩P·M)) = ℓ(N/P·N) - ℓ((N∩P·M)/P·N)`. The snake construction applied to `·P` on
`0 → N → M → T → 0`, using `M[P] = 0` (`hP`), shows the connecting map
`T[P] → (N ∩ P·M)/P·N` is an isomorphism. Finally `0 → T[P] → T --·P--> T → T/P·T → 0`
(with `T` of finite length) gives `ℓ(T/P·T) = ℓ(T[P])`. Substituting, the two correction terms
cancel and `ℓ(M/P·M) = ℓ(N/P·N) = ℓ(B ⧸ (𝔭 + (P)))`.

(Formalised directly in terms of `B`-modules, i.e. without changing scalars to `A := B ⧸ 𝔭`; the
whole chain `h1`–`h5` is `Work.BW.rank_one_cut_length`'s argument, and the final identification
`N ⧸ P·N ≅ B ⧸ (𝔭 + (P))` is proved from the explicit map `b ↦ b·m₀`.) -/
theorem rank_one_cut_bound {B : Type*} [CommRing B] (𝔭 : Ideal B) (P : B)
    {M : Type*} [AddCommGroup M] [Module B M] (m₀ : M)
    (hann : ∀ b ∈ 𝔭, ∀ m : M, b • m = 0)
    (hP : ∀ m : M, P • m = 0 → m = 0)
    (hx : ∀ b : B, b • m₀ = 0 → b ∈ 𝔭)
    (hfin : IsFiniteLength B (M ⧸ (Submodule.span B {m₀}))) :
    Module.length B (M ⧸ (Ideal.span {P} • (⊤ : Submodule B M))) =
      Module.length B (B ⧸ (𝔭 ⊔ Ideal.span {P})) := by
  set N : Submodule B M := Submodule.span B {m₀} with hN
  have hmN : m₀ ∈ N := by rw [hN]; exact Submodule.subset_span (Set.mem_singleton m₀)
  -- `length (M ⧸ P·M) = length (M ⧸ (N + P·M)) + length ((N + P·M) ⧸ P·M)`
  have h1 : Module.length B (M ⧸ cutPM (M := M) P) =
      Module.length B (M ⧸ cutSup P N) +
        Module.length B (cutSup P N ⧸ (cutPM (M := M) P).comap (cutSup P N).subtype) :=
    length_quotient_add _ _ le_sup_right
  -- second isomorphism theorem: `(N + P·M)/P·M ≅ N/(N ∩ P·M)`
  have hiso : Module.length B (N ⧸ cutQ P N) =
      Module.length B (cutSup P N ⧸ (cutPM (M := M) P).comap (cutSup P N).subtype) := by
    have h := (LinearMap.quotientInfEquivSupQuotient N (cutPM (M := M) P)).length_eq
    rw [Submodule.comap_subtype_self, top_inf_eq] at h
    rw [cutQ, cutSup]
    convert h using 2
  -- third isomorphism theorem: `M/(N + P·M) ≅ (M ⧸ N) ⧸ P·(M ⧸ N)`
  have h2 : Module.length B (M ⧸ cutSup P N) =
      Module.length B ((M ⧸ N) ⧸ (cutMap P N).range) := cut_sup_length P N
  -- kernel and cokernel of `P·` on the finite-length module `M ⧸ N` have equal length
  have h3 : Module.length B (cutMap P N).ker =
      Module.length B ((M ⧸ N) ⧸ (cutMap P N).range) :=
    length_ker_eq_length_coker (cutMap P N) hfin
  -- `(N ∩ P·M)/P·N ≅ ker (P·)`, using `P`-torsion-freeness of `M`
  have h4 : Module.length B (cutQ P N ⧸ cutPNQ P N) = Module.length B (cutMap P N).ker :=
    cut_torsion_length P N hP
  -- `N/P·N` is an extension of `N/(N ∩ P·M)` by `(N ∩ P·M)/P·N`
  have h5 : Module.length B (N ⧸ cutPN P N) =
      Module.length B (N ⧸ cutQ P N) + Module.length B (cutQ P N ⧸ cutPNQ P N) :=
    length_quotient_add (cutPN P N) (cutQ P N) (cutPN_le_cutQ P N)
  -- `b ↦ b·m₀` induces `B ⧸ (𝔭 + (P)) ≅ N ⧸ P·N`
  have h6 : Module.length B (N ⧸ cutPN P N) = Module.length B (B ⧸ (𝔭 ⊔ Ideal.span {P})) := by
    have hcutPN : cutPN P N = (LinearMap.lsmul B N P).range := by
      rw [cutPN, Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def,
        Submodule.map_top]
      rfl
    let φ : B →ₗ[B] N := LinearMap.toSpanSingleton B N ⟨m₀, hmN⟩
    let f : B →ₗ[B] N ⧸ cutPN P N := (cutPN P N).mkQ.comp φ
    have hf : ∀ b : B, f b = (cutPN P N).mkQ ⟨b • m₀, N.smul_mem b hmN⟩ := by
      intro b
      show (cutPN P N).mkQ (φ b) = _
      rw [LinearMap.toSpanSingleton_apply]
      rfl
    have hker : f.ker = 𝔭 ⊔ Ideal.span {P} := by
      ext b
      rw [LinearMap.mem_ker]
      constructor
      · -- `f b = 0` means `⟨b·m₀, _⟩ ∈ P·N`, i.e. `P·y = b·m₀` for some `y = d·m₀`
        intro hb
        rw [hf b, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hb
        rw [hcutPN, LinearMap.mem_range] at hb
        obtain ⟨y, hy⟩ := hb
        have hy' : P • (y : M) = b • m₀ := by
          have := congrArg (fun t : N => (t : M)) hy
          simpa using this
        have hyspan : (y : M) ∈ B ∙ m₀ := y.2
        obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hyspan
        have hbP : (b - P * d) • m₀ = 0 := by
          rw [sub_smul, mul_smul, hd, hy', sub_self]
        have hmem : b - P * d ∈ 𝔭 := hx _ hbP
        rw [Submodule.mem_sup]
        exact ⟨b - P * d, hmem, P * d, Ideal.mem_span_singleton.mpr ⟨d, rfl⟩, by ring⟩
      · -- `b = y + z` with `y ∈ 𝔭`, `z ∈ (P)`: both have `f y = 0`, `f z = 0`
        intro hb
        rw [Submodule.mem_sup] at hb
        obtain ⟨y, hy, z, hz, hyz⟩ := hb
        rw [← hyz, map_add]
        have hy0 : f y = 0 := by
          rw [hf y, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          have hz' : (⟨y • m₀, N.smul_mem y hmN⟩ : N) = 0 :=
            Subtype.ext (hann y hy m₀)
          rw [hz']
          exact Submodule.zero_mem _
        have hz0 : f z = 0 := by
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hz
          rw [hf (P * c), Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          rw [cutPN]
          have h1 : P ∈ Ideal.span ({P} : Set B) := Ideal.mem_span_singleton.mpr ⟨1, by ring⟩
          have hmem : P • (⟨c • m₀, N.smul_mem c hmN⟩ : N)
              ∈ Ideal.span ({P} : Set B) • (⊤ : Submodule B N) :=
            Submodule.smul_mem_smul h1 Submodule.mem_top
          have heq : (⟨(P * c) • m₀, N.smul_mem (P * c) hmN⟩ : N)
              = P • (⟨c • m₀, N.smul_mem c hmN⟩ : N) := by
            ext; simp [mul_smul]
          rw [heq]
          exact hmem
        rw [hy0, hz0, add_zero]
    have hsurj : Function.Surjective f := by
      intro x
      obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective (p := cutPN P N) x
      rw [← hn]
      have hnmem : (n : M) ∈ B ∙ m₀ := n.2
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hnmem
      refine ⟨d, ?_⟩
      rw [hf d, Submodule.mkQ_apply]
      congr 1
      exact Subtype.ext hd
    have e := LinearMap.quotKerEquivOfSurjective f hsurj
    rw [hker] at e
    exact e.length_eq.symm
  calc Module.length B (M ⧸ cutPM (M := M) P)
      = Module.length B (M ⧸ cutSup P N) +
          Module.length B (cutSup P N ⧸ (cutPM (M := M) P).comap (cutSup P N).subtype) := h1
    _ = Module.length B (M ⧸ cutSup P N) + Module.length B (N ⧸ cutQ P N) := by rw [hiso]
    _ = Module.length B ((M ⧸ N) ⧸ (cutMap P N).range) +
          Module.length B (N ⧸ cutQ P N) := by rw [h2]
    _ = Module.length B (cutMap P N).ker + Module.length B (N ⧸ cutQ P N) := by rw [← h3]
    _ = Module.length B (cutQ P N ⧸ cutPNQ P N) + Module.length B (N ⧸ cutQ P N) := by rw [← h4]
    _ = Module.length B (N ⧸ cutQ P N) + Module.length B (cutQ P N ⧸ cutPNQ P N) := add_comm _ _
    _ = Module.length B (N ⧸ cutPN P N) := by rw [← h5]
    _ = Module.length B (B ⧸ (𝔭 ⊔ Ideal.span {P})) := h6

end Work.BW
