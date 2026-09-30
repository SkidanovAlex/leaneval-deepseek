import Mathlib
import Submission.Work.BW.kummer_setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Crux for the multi-quadratic Kummer independence lemma (`Work.BW.kummer_indep`).

The argument is the sign / `ℤ/2`-grading argument: writing `T d = ∑ ε, φ (d ε) * B_ε` with
`B_ε = ∏ i, ρ i ^ (ε i:ℕ)`, the products satisfy `B_ε * B_δ = φ (∏ i, η i ^ (ε i * δ i)) * B_{ε+δ}`
(`Bfun_mul`), so `T` is a ring homomorphism.  Splitting the coefficients according to the value of
a fixed coordinate `ε i` exhibits `x = T c = U + V` with `U` supported on `ε i = 0` and `V`
supported on `ε i = 1`; from `x ^ 2 = φ a₀ ∈ K` one deduces `U * V = 0`, whence `U - V = ± x`
and the coordinate `i` is constant on the support of `c`.  Doing this for every `i` shows the
support of `c` is a single point `γ`, and then `a₀ * ∏ i, η i ^ (γ i)` is a square. -/

namespace Work.BW

open Finset

private theorem sign_factor {U V : ℂ} (hUV : U * V = 0) :
    ((U - V) - (U + V)) * ((U - V) + (U + V)) = 0 := by
  have h : (U - V) ^ 2 = (U + V) ^ 2 := by
    have h1 : (U - V) ^ 2 - (U + V) ^ 2 = -4 * (U * V) := by ring
    rw [← sub_eq_zero, h1, hUV]; ring
  calc ((U - V) - (U + V)) * ((U - V) + (U + V))
      = (U - V) ^ 2 - (U + V) ^ 2 := by ring
    _ = 0 := by rw [h]; ring

private theorem sub_sign_eq_zero {U V : ℂ} (h : (U - V) - (U + V) = 0) : V = 0 := by
  have h1 : (U - V) - (U + V) = -2 * V := by ring
  rw [h1] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

private theorem add_sign_eq_zero {U V : ℂ} (h : (U - V) + (U + V) = 0) : U = 0 := by
  have h1 : (U - V) + (U + V) = 2 * U := by ring
  rw [h1] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

private theorem two_UV_eq {U V a0 : ℂ} (hx : (U + V) ^ 2 = a0) :
    (a0 - U * U) - V * V = 2 * (U * V) := by
  rw [← hx]; ring

/-- Crux for multi-quadratic Kummer independence (see `Work.BW.kummer_indep`). If
`x = ∑_ε φ(c_ε) ∏_i ρ_i^{ε_i}` (a `φ(K)`-linear combination of the `2^r` products of the chosen
square roots `ρ_i² = φ(η_i)`) satisfies `x ^ 2 = φ a₀`, and the `2^r` products are linearly
independent over `φ(K)` (hypothesis `hind`), then `a₀` times some product `∏_i η_i^{γ_i}` is a
square in `K`.

Route (sign/`ℤ/2`-grading, no automorphisms needed). Let `S := span_K{∏_i ρ_i^{ε_i}}`; one has
`B_ε * B_δ = φ(∏_i η_i^{ε_i·δ_i}) * B_{ε+δ}` where `+` is pointwise in `Fin 2 = ℤ/2`, so `S` is a
subalgebra. For fixed `i`, let `W₀`/`W₁` be the spans of `{B_ε : ε_i = 0}` / `{B_ε : ε_i = 1}`; then
`W₀·W₀ ⊆ W₀`, `W₁·W₁ ⊆ W₀`, `W₀·W₁ ⊆ W₁`, and `W₀ ⊓ W₁ = ⊥` (the latter by `hind`). Split
`x = U + V` with `U = ∑_{ε_i=0} φ(c_ε)B_ε ∈ W₀`, `V = ∑_{ε_i=1} φ(c_ε)B_ε ∈ W₁`. As `x² = φ a₀ ∈ K`
and `U², V² ∈ W₀`, `2UV = x² - U² - V² ∈ W₀` while `UV ∈ W₁`, so `UV = 0` and `y := U - V` has
`y² = U² - 2UV + V² = x²`, whence `y = ±x`. `y = x` forces `V = 0`, `y = -x` forces `U = 0`; by
`hind` this kills all `c_ε` with `ε_i` of one parity, so every coordinate `ε_i` is constant on the
support of `c`, i.e. the support is a single `γ`. Then `x = φ(c_γ)B_γ` and
`φ a₀ = x² = φ(c_γ² ∏_i η_i^{γ_i})`, giving `u = c_γ · ∏_i η_i^{γ_i}`. The case `x = 0` gives
`a₀ = 0`, `u = 0`. -/
theorem kummer_crux {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (η : Fin r → K) (ρ : Fin r → ℂ)
    (hρ : ∀ i, ρ i ^ 2 = φ (η i))
    (hind : ∀ (b : (Fin r → Fin 2) → K),
      (∑ ε, φ (b ε) * ∏ i, ρ i ^ (ε i : ℕ)) = 0 → b = 0)
    (c : (Fin r → Fin 2) → K) (a0 : K)
    (hx : (∑ ε, φ (c ε) * ∏ i, ρ i ^ (ε i : ℕ)) ^ 2 = φ a0) :
    ∃ (γ : Fin r → Fin 2) (u : K), a0 * (∏ i, η i ^ (γ i : ℕ)) = u ^ 2 := by
  classical
  have hxT : Tfun φ ρ c ^ 2 = φ a0 := by simpa [Tfun, Bfun] using hx
  have hind' : ∀ b : (Fin r → Fin 2) → K, Tfun φ ρ b = 0 → b = 0 :=
    fun b hb => hind b (by simpa [Tfun, Bfun] using hb)
  -- Step 1: for each coordinate `i`, the value `ε i` is constant on the support of `c`.
  have hcoord : ∀ i : Fin r, (∀ ε, ε i = 1 → c ε = 0) ∨ (∀ ε, ε i = 0 → c ε = 0) := by
    intro i
    set c0 : (Fin r → Fin 2) → K := fun ε => if ε i = 0 then c ε else 0 with hc0def
    set c1 : (Fin r → Fin 2) → K := fun ε => if ε i = 1 then c ε else 0 with hc1def
    have hc0 : Supp i 0 c0 := by
      intro ε hε; simp [hc0def, hε]
    have hc1 : Supp i 1 c1 := by
      intro ε hε; simp [hc1def, hε]
    have hc01 : c0 + c1 = c := by
      funext ε
      rcases fin2_eq_zero_or_one (ε i) with h | h <;> simp [hc0def, hc1def, h]
    have hxUV : Tfun φ ρ c = Tfun φ ρ c0 + Tfun φ ρ c1 := by
      rw [← hc01, Tfun_add]
    have hU : Tfun φ ρ (cMul η c0 c0) = Tfun φ ρ c0 * Tfun φ ρ c0 :=
      (Tfun_cMul φ η ρ hρ c0 c0).symm
    have hV : Tfun φ ρ (cMul η c1 c1) = Tfun φ ρ c1 * Tfun φ ρ c1 :=
      (Tfun_cMul φ η ρ hρ c1 c1).symm
    have hUV' : Tfun φ ρ (cMul η c0 c1) = Tfun φ ρ c0 * Tfun φ ρ c1 :=
      (Tfun_cMul φ η ρ hρ c0 c1).symm
    have hp00 : Supp i 0 (cMul η c0 c0) := by
      simpa [fin2_zero_add_zero] using cMul_supp η i c0 c0 0 0 hc0 hc0
    have hp11 : Supp i 0 (cMul η c1 c1) := by
      simpa [fin2_one_add_one] using cMul_supp η i c1 c1 1 1 hc1 hc1
    have hp01 : Supp i 1 (cMul η c0 c1) := by
      simpa [fin2_zero_add_one] using cMul_supp η i c0 c1 0 1 hc0 hc1
    set δ0 : (Fin r → Fin 2) → K := fun ε => if ε = 0 then a0 else 0 with hδdef
    have hδ0 : Supp i 0 δ0 := by
      intro ε hε
      have hne : ε ≠ (0 : Fin r → Fin 2) := fun h => hε (by rw [h]; rfl)
      simp [hδdef, hne]
    have hTδ : Tfun φ ρ δ0 = φ a0 := by rw [hδdef]; exact Tfun_single φ ρ a0
    set P : (Fin r → Fin 2) → K := δ0 - cMul η c0 c0 - cMul η c1 c1 with hPdef
    set Q : (Fin r → Fin 2) → K := (2 : K) • cMul η c0 c1 with hQdef
    have hP0 : Supp i 0 P := by
      rw [hPdef]
      exact Supp.sub i 0 (Supp.sub i 0 hδ0 hp00) hp11
    have hQ1 : Supp i 1 Q := by
      rw [hQdef]
      exact Supp.smul i 1 (2 : K) hp01
    have hTP : Tfun φ ρ P = 2 * (Tfun φ ρ c0 * Tfun φ ρ c1) := by
      rw [hPdef, Tfun_sub, Tfun_sub, hTδ, hU, hV]
      have hxloc : (Tfun φ ρ c0 + Tfun φ ρ c1) ^ 2 = φ a0 := by
        rw [← hxUV]; exact hxT
      exact two_UV_eq hxloc
    have hTQ : Tfun φ ρ Q = 2 * (Tfun φ ρ c0 * Tfun φ ρ c1) := by
      rw [hQdef, Tfun_smul, hUV', map_ofNat]
    have hPQ : P = Q := by
      have h : Tfun φ ρ (P - Q) = 0 := by rw [Tfun_sub, hTP, hTQ, sub_self]
      exact sub_eq_zero.mp (hind' (P - Q) h)
    have hP1 : Supp i 1 P := by rw [hPQ]; exact hQ1
    have hPz : P = 0 := Supp_disjoint i (by decide) hP0 hP1
    have hUV0 : Tfun φ ρ c0 * Tfun φ ρ c1 = 0 := by
      have h2 : (2 : ℂ) * (Tfun φ ρ c0 * Tfun φ ρ c1) = 0 := by
        rw [← hTP, hPz, Tfun_zero]
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    rcases mul_eq_zero.mp (sign_factor hUV0) with hcase | hcase
    · left
      have hV0 : Tfun φ ρ c1 = 0 := sub_sign_eq_zero hcase
      have hc1z : c1 = 0 := hind' c1 hV0
      intro ε hε
      have h1 : c1 ε = 0 := congrFun hc1z ε
      rw [hc1def] at h1
      simpa [hε] using h1
    · right
      have hU0 : Tfun φ ρ c0 = 0 := add_sign_eq_zero hcase
      have hc0z : c0 = 0 := hind' c0 hU0
      intro ε hε
      have h1 : c0 ε = 0 := congrFun hc0z ε
      rw [hc0def] at h1
      simpa [hε] using h1
  -- Step 2: the support of `c` is a single point.
  by_cases hker : ∃ ε, c ε ≠ 0
  · obtain ⟨γ, hγ⟩ := hker
    have huniq : ∀ ε, c ε ≠ 0 → ε = γ := by
      intro ε hε
      funext i
      rcases hcoord i with h | h
      · have he : ε i = 0 := fin2_ne_one _ (fun hc => hε (h ε hc))
        have hg : γ i = 0 := fin2_ne_one _ (fun hc => hγ (h γ hc))
        rw [he, hg]
      · have he : ε i = 1 := fin2_ne_zero _ (fun hc => hε (h ε hc))
        have hg : γ i = 1 := fin2_ne_zero _ (fun hc => hγ (h γ hc))
        rw [he, hg]
    have hc_single : ∀ ε, ε ≠ γ → c ε = 0 := by
      intro ε hε
      by_contra hne
      exact hε (huniq ε hne)
    have hTc : Tfun φ ρ c = φ (c γ) * Bfun ρ γ := Tfun_eq_single φ ρ c γ hc_single
    have hsq : (φ (c γ) * Bfun ρ γ) ^ 2 = φ a0 := by rw [← hTc]; exact hxT
    have hsq2 : φ (c γ ^ 2 * ∏ i, η i ^ (γ i : ℕ)) = φ a0 := by
      rw [map_mul, map_pow, ← Bfun_sq φ η ρ hρ γ, ← hsq]
      ring
    have ha0 : a0 = c γ ^ 2 * ∏ i, η i ^ (γ i : ℕ) := (RingHom.injective φ) hsq2.symm
    exact ⟨γ, c γ * ∏ i, η i ^ (γ i : ℕ), by rw [ha0]; ring⟩
  · push Not at hker
    have hc0 : c = 0 := funext hker
    have hzero : Tfun φ ρ c = 0 := by rw [hc0]; exact Tfun_zero φ ρ
    have h0 : φ a0 = 0 := by rw [← hxT, hzero]; ring
    refine ⟨0, 0, ?_⟩
    have ha0 : a0 = 0 := (RingHom.injective φ) (by rw [h0, map_zero])
    rw [ha0]; simp

end Work.BW
