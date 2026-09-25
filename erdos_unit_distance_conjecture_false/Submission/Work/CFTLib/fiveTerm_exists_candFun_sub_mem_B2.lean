import Mathlib
import Submission.Work.CFTLib.fiveTerm_setup

/-!
# Exactness of the five-term sequence at `H²(G, 𝔽_p)`

Let `π : G' →* G` be a surjective homomorphism of groups with kernel `N = π.ker`.  The
five-term inflation–restriction sequence of the extension

`H¹(G) →^{inf} H¹(G') →^{res} H¹(N)^{G'} →^{tg} H²(G) →^{inf} H²(G')`

is exact at `H²(G)`: the kernel of inflation is the image of the transgression.  Since
inflation is nothing but pullback `precomp₂ π` of `2`-cochains and the transgression is
computed by the cocycle `candFun π hπ t` attached to an invariant character `t` of `N`
(using a set-theoretic section of `π`), the exactness at `H²(G)` reads

> if `z ∈ Z²(G, 𝔽_p)` and `precomp₂ π z = d₁₂ b` for some `1`-cochain `b` of `G'`
> (that is, the inflation of `z` is a coboundary), then `z - candFun π hπ t` is a
> coboundary for some `t ∈ Hom(N, 𝔽_p)^{G'}`.

This is the content of `fiveTerm_exists_candFun_sub_mem_B2` below.

The proof is a completely explicit cocycle computation; no finiteness of the groups is
used.  Writing `κ = b 1` (which equals `z (1,1)` and the constant value of `z (·,1)` and
`z (1,·)` on a `2`-cocycle), the relations

* `b (u * m) = b u + b m - κ` for `u ∈ G'`, `m ∈ N`,
* `b (m * u) = b u + b m - κ` for `u ∈ G'`, `m ∈ N`,
* `b (g * n * g⁻¹) = b n` for `g ∈ G'`, `n ∈ N`,

hold, the second and third being consequences of the first.  They say precisely that
`t : n ↦ b n - κ` is an additive homomorphism `N → 𝔽_p`, invariant under conjugation by
`G'`.  With `a : x ↦ b (σ x)` the `1`-cochain of `G` attached to a section `σ` of `π`,
the identity `σ x * σ y = c(x,y) * σ (x*y)` (with `c(x,y) = factor π hπ x y`) turns the
cocycle relation satisfied by `z` into

`z - candFun π hπ t = d₁₂ a`,

whence the conclusion.
-/

namespace Work.CFTLib

open CategoryTheory Representation groupCohomology
open scoped Classical

noncomputable section

theorem fiveTerm_exists_candFun_sub_mem_B2 {p : ℕ} [Fact p.Prime] {G G' : Type} [Group G]
    [Group G'] (π : G' →* G) (hπ : Function.Surjective π) (z : G × G → ZMod p)
    (hz : z ∈ Work.CFTLib.Z2 p G) (b : G' → ZMod p)
    (hb : Work.CFTLib.precomp₂ π z = Work.CFTLib.d12 p G' b) :
    ∃ t : Work.CFTLib.invCharSubmodule p π.ker,
      z - Work.CFTLib.candFun π hπ t ∈ Work.CFTLib.B2 p G := by
  -- The cocycle relation for `z`, written out.
  have hz_coc : ∀ x y w : G, z (y, w) - z (x * y, w) + z (x, y * w) - z (x, y) = 0 := by
    intro x y w
    have h := (mem_cocycles₂_def (A := Rep.trivial (ZMod p) G (ZMod p)) z).1 hz x y w
    simpa using h
  -- A `2`-cocycle has `z (x, 1) = z (1, y) = z (1, 1)`.
  have hz_fst : ∀ x : G, z (x, 1) = z (1, 1) := by
    intro x
    have h := hz_coc x 1 1
    simp only [mul_one] at h
    have h2 : z (1, 1) - z (x, 1) = 0 := by simpa using h
    exact (sub_eq_zero.mp h2).symm
  have hz_snd : ∀ y : G, z (1, y) = z (1, 1) := by
    intro y
    have h := hz_coc 1 1 y
    simp only [mul_one, one_mul] at h
    have h2 : z (1, y) - z (1, 1) = 0 := by simpa using h
    exact sub_eq_zero.mp h2
  -- The hypothesis `hb`, written out.
  have hb_apply : ∀ u v : G', z (π u, π v) = b v - b (u * v) + b u := by
    intro u v
    have h := congrFun hb (u, v)
    simpa [precomp₂_apply, d12, d₁₂_hom_apply] using h
  have hb_one : b 1 = z (1, 1) := by
    have h := hb_apply 1 1
    simpa using h.symm
  -- Multiplication by an element of the kernel on the right.
  have hb_mul_right : ∀ (u : G') (m : π.ker), b (u * m) = b u + b m - b 1 := by
    intro u m
    have h := hb_apply u (m : G')
    rw [m.2, hz_fst (π u), ← hb_one] at h
    rw [h]; abel
  -- Multiplication by an element of the kernel on the left.
  have hb_mul_left : ∀ (m : π.ker) (u : G'), b (m * u) = b u + b m - b 1 := by
    intro m u
    have h := hb_apply (m : G') u
    rw [m.2, hz_snd (π u), ← hb_one] at h
    rw [h]; abel
  -- `b` is invariant under conjugation.
  have hb_conj : ∀ (g : G') (n : π.ker), b (g * (n : G') * g⁻¹) = b (n : G') := by
    intro g n
    have hmem : g * (n : G') * g⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, n.2]
      simp
    have h1 := hb_mul_right g n
    have h2 := hb_mul_left (⟨g * (n : G') * g⁻¹, hmem⟩ : π.ker) g
    have h3 : ((⟨g * (n : G') * g⁻¹, hmem⟩ : π.ker) : G') * g = g * (n : G') := by
      simp [mul_assoc]
    rw [h3] at h2
    have heq : b g + b (n : G') - b 1
        = b g + b ((⟨g * (n : G') * g⁻¹, hmem⟩ : π.ker) : G') - b 1 :=
      h1.symm.trans h2
    have heq3 : b (n : G') - b 1
        = b ((⟨g * (n : G') * g⁻¹, hmem⟩ : π.ker) : G') - b 1 :=
      add_left_cancel (by simpa only [add_sub_assoc] using heq)
    exact (sub_left_inj.mp heq3).symm
  -- The invariant character `t : n ↦ b n - b 1` of `N = π.ker`.
  let tHom : Additive π.ker →+ ZMod p :=
    { toFun := fun n => b (n.toMul : G') - b 1
      map_zero' := by simp
      map_add' := by
        intro x y
        have h := hb_mul_right (x.toMul : G') y.toMul
        rw [toMul_add, Subgroup.coe_mul, h]
        ring }
  have htHom_apply : ∀ n : π.ker, tHom (Additive.ofMul n) = b (n : G') - b 1 :=
    fun n => rfl
  have ht : tHom ∈ invCharSubmodule p π.ker := by
    intro g n
    have hbc : b (g⁻¹ * (n : G') * g) = b (n : G') := by simpa using hb_conj g⁻¹ n
    rw [htHom_apply, htHom_apply, hbc]
  refine ⟨⟨tHom, ht⟩, ?_⟩
  -- The `1`-cochain `a : x ↦ b (σ x)` of `G`; we show `d₁₂ a = z - candFun π hπ t`.
  refine ⟨fun x => b (sectionOf π hπ x), ?_⟩
  funext x
  obtain ⟨x₁, x₂⟩ := x
  have hd12 : d12 p G (fun x => b (sectionOf π hπ x)) (x₁, x₂)
      = b (sectionOf π hπ x₂) - b (sectionOf π hπ (x₁ * x₂)) + b (sectionOf π hπ x₁) := by
    simp [d12, d₁₂_hom_apply]
  have hcand : candFun π hπ (⟨tHom, ht⟩ : invCharSubmodule p π.ker) (x₁, x₂)
      = b 1 - b ((factor π hπ x₁ x₂ : π.ker) : G') := by
    rw [candFun_apply, htHom_apply]
    ring
  have hkey1 : z (x₁, x₂) = b (sectionOf π hπ x₂)
      - b (sectionOf π hπ x₁ * sectionOf π hπ x₂) + b (sectionOf π hπ x₁) := by
    have h := hb_apply (sectionOf π hπ x₁) (sectionOf π hπ x₂)
    rw [sectionOf_spec, sectionOf_spec] at h
    exact h
  have hsplit : sectionOf π hπ x₁ * sectionOf π hπ x₂
      = ((factor π hπ x₁ x₂ : π.ker) : G') * sectionOf π hπ (x₁ * x₂) := by
    rw [factor_coe]; group
  have hkey2 : b (sectionOf π hπ x₁ * sectionOf π hπ x₂)
      = b (sectionOf π hπ (x₁ * x₂)) + b ((factor π hπ x₁ x₂ : π.ker) : G') - b 1 := by
    rw [hsplit]
    exact hb_mul_left (factor π hπ x₁ x₂) (sectionOf π hπ (x₁ * x₂))
  rw [Pi.sub_apply, hd12, hcand, hkey1, hkey2]
  ring

end

end Work.CFTLib
