import Mathlib
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open scoped Pointwise

/-! ## The twisted `1`-coboundary and its calculus -/

section Basic

variable {G : Type} [Group G] {M : Type} [AddCommGroup M] [DistribMulAction G M]

/-- The twisted `1`-coboundary `(δβ)(g,h) = g • β h - β (g*h) + β g`. -/
def dlt (β : G → M) (g h : G) : M := g • β h - β (g * h) + β g

lemma dlt_add (β γ : G → M) (g h : G) :
    dlt (β + γ) g h = dlt β g h + dlt γ g h := by
  simp only [dlt, Pi.add_apply, smul_add]; abel

lemma dlt_cocycle (β : G → M) : SSGRoute.IsCocycle2 (MonoidHom.id G) (dlt β) := by
  intro g h l
  simp only [dlt, MonoidHom.id_apply, smul_sub, smul_add, mul_smul]
  rw [mul_assoc]; abel

lemma coc_sub {c c' : G → G → M}
    (hc : SSGRoute.IsCocycle2 (MonoidHom.id G) c) (hc' : SSGRoute.IsCocycle2 (MonoidHom.id G) c') :
    SSGRoute.IsCocycle2 (MonoidHom.id G) (fun g h => c g h - c' g h) := by
  intro g h l
  have h1 := hc g h l
  have h2 := hc' g h l
  simp only [MonoidHom.id_apply] at h1 h2 ⊢
  have key : g • (c h l - c' h l) - (c (g * h) l - c' (g * h) l)
        + (c g (h * l) - c' g (h * l)) - (c g h - c' g h)
      = (g • c h l - c (g * h) l + c g (h * l) - c g h)
        - (g • c' h l - c' (g * h) l + c' g (h * l) - c' g h) := by
    rw [smul_sub]; abel
  rw [key, h1, h2, sub_zero]

lemma isCocycle2_id_iff {c : G → G → M} :
    SSGRoute.IsCocycle2 (MonoidHom.id G) c ↔
      ∀ g h l : G, g • c h l - c (g * h) l + c g (h * l) - c g h = 0 := by
  simp only [SSGRoute.IsCocycle2, MonoidHom.id_apply]

lemma solve_b {a b c d : M} (h : a - b + c - d = 0) : b = a + c - d := by
  have h' : a - b + c = d := sub_eq_zero.mp h
  rw [← h']; abel

lemma solve_cc {a b c d : M} (h : a - b + c - d = 0) : c = d - a + b := by
  have h' : a - b + c = d := sub_eq_zero.mp h
  rw [← h']; abel

lemma solve_a {a b c d : M} (h : a - b + c - d = 0) : a = d - c + b := by
  have h' : a - b + c = d := sub_eq_zero.mp h
  rw [← h']; abel

lemma smul_eq_zero_of {g : G} {m : M} (h : g • m = 0) : m = 0 := by
  have h2 : g⁻¹ • (g • m) = g⁻¹ • (0 : M) := congrArg _ h
  rw [← mul_smul, inv_mul_cancel, one_smul, smul_zero] at h2
  exact h2

end Basic

/-! ## Averaging a crossed homomorphism over a finite group -/

section Average

variable {W : Type} [Group W] [Fintype W] {M : Type} [AddCommGroup M] {p : ℕ}
  [Fact p.Prime] [Module (ZMod p) M] [DistribMulAction W M] [SMulCommClass W (ZMod p) M]

/-- **Averaging a crossed homomorphism.**  If `f : W → M` satisfies
`f (a*b) = a • f b + f a` and `|W|` is invertible in `𝔽_p`, then `f` is the coboundary of the
average `γ := -|W|⁻¹ • ∑ f`, i.e. `f w = w • γ - γ` for all `w : W`. -/
lemma crossed_hom_average
    (hcop : Nat.Coprime (Fintype.card W) p) (f : W → M)
    (hf : ∀ a b : W, f (a * b) = a • f b + f a) :
    ∃ γ : M, γ = - ( (((Fintype.card W : ℕ) : ZMod p))⁻¹ • (∑ u : W, f u) ) ∧
      ∀ w : W, f w = w • γ - γ := by
  have hunit : IsUnit (((Fintype.card W : ℕ) : ZMod p)) :=
    (ZMod.isUnit_iff_coprime (Fintype.card W) p).mpr hcop
  have hne : (((Fintype.card W : ℕ) : ZMod p)) ≠ 0 := hunit.ne_zero
  have hcancel : ∀ x : M, (((Fintype.card W : ℕ) : ZMod p))⁻¹ • ((((Fintype.card W : ℕ) : ZMod p)) • x) = x := by
    intro x; rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  let S : M := ∑ u : W, f u
  let γ : M := - ( (((Fintype.card W : ℕ) : ZMod p))⁻¹ • S )
  refine ⟨γ, rfl, fun w => ?_⟩
  have hS : S = w • S + ((Fintype.card W : ℕ) : ZMod p) • f w := by
    show (∑ u : W, f u) = w • (∑ u : W, f u) + ((Fintype.card W : ℕ) : ZMod p) • f w
    calc (∑ u : W, f u) = ∑ u : W, f (w * u) := (Equiv.sum_comp (Equiv.mulLeft w) f).symm
      _ = ∑ u : W, (w • f u + f w) := Finset.sum_congr rfl (fun u _ => hf w u)
      _ = w • (∑ u : W, f u) + ∑ _u : W, f w := by
            rw [Finset.sum_add_distrib, Finset.smul_sum]
      _ = w • (∑ u : W, f u) + ((Fintype.card W : ℕ) : ZMod p) • f w := by
            rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hNsmul : (((Fintype.card W : ℕ) : ZMod p)) • f w = S - w • S := by
    nth_rewrite 1 [hS]; abel
  have hfw : f w = ((((Fintype.card W : ℕ) : ZMod p))⁻¹ • S) - w • ((((Fintype.card W : ℕ) : ZMod p))⁻¹ • S) := by
    rw [← hcancel (f w), hNsmul, smul_sub, (smul_comm w (((Fintype.card W : ℕ) : ZMod p))⁻¹ S).symm]
  show f w = w • γ - γ
  rw [show γ = - ( (((Fintype.card W : ℕ) : ZMod p))⁻¹ • S ) from rfl, hfw, smul_neg]; abel

end Average

/-- **Descent of a `2`-cocycle along a normal subgroup of order prime to `p` whose restriction is
a coboundary.**

`G` a group, `W ⊴ G` a finite normal subgroup with `Nat.Coprime (Nat.card W) p` (`hcop`),
`M` a finite `𝔽_p`-module on which `G` acts (`SMulCommClass G (ZMod p) M`).  If `c : G → G → M`
is a `2`-cocycle (`SSGRoute.IsCocycle2` with `act = id`) whose restriction to `W` is a coboundary
on `W` (witness `b`), then `c` differs from the inflation of a `2`-cocycle `c₀` on `G/W` (with
values in `M^W`) by a coboundary `δβ`:

the conclusion exhibits `β : G → M` and `c₀ : G ⧸ W → G ⧸ W → M` with
* `c₀` a `2`-cocycle on `G/W` for the representative-level action `(g : G) • _` (its values are
  `W`-fixed, so this is well defined on cosets),
* all values `c₀ x y` fixed by `W`,
* `c g h = (g • β h - β (g*h) + β g) + c₀ (mk g) (mk h)` for all `g h : G`.

This is the cochain-level form of the inflation–restriction exactness
`ker(H²(G,M) → H²(W,M)) = im(H²(G/W, M^W) → H²(G,M))`, which holds because `p ∤ |W|` and hence
`H^q(W,M) = 0` for `q ≥ 1` (averaging/Maschke).
Route: with `e := c - δβ` vanishing on `W × W` and `θ g := (1/|W|) Σ_{w ∈ W} e (g,w)` (the
average over `W`, whose order is invertible in `𝔽_p`) one checks `δθ (g,w) = e (g,w)` for all
`g : G`, `w ∈ W`, so that `e' := e - δθ` vanishes on `G × W`; then `e'` is right-`W`-invariant
and descends to a cocycle on `G/W` with values in `M^W`, explicitly
`c₀ (mk g) (mk h) := e' (g,h)`.  The multiplicativity of the action (`SMulCommClass`) is used in
the averaging step. -/
theorem descentInflationFinite
    (p : ℕ) [Fact p.Prime] {G : Type} [Group G] (W : Subgroup G) [W.Normal] [Finite W]
    (hcop : Nat.Coprime (Nat.card W) p)
    {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    (c : G → G → M) (hc : _root_.SSGRoute.IsCocycle2 (MonoidHom.id G) c)
    (hW : ∃ b : W → M, ∀ w w' : W, c (w : G) (w' : G) = (w : G) • b w' - b (w * w') + b w) :
    ∃ (β : G → M) (c₀ : G ⧸ W → G ⧸ W → M),
      (∀ g h l : G, (g : G) • c₀ (QuotientGroup.mk' W h) (QuotientGroup.mk' W l)
          - c₀ (QuotientGroup.mk' W (g * h)) (QuotientGroup.mk' W l)
          + c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W (h * l))
          - c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W h) = 0) ∧
      (∀ g h : G, ∀ w : W, (w : G) • c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W h)
          = c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W h)) ∧
      (∀ g h : G, c g h = (g • β h - β (g * h) + β g)
          + c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W h)) := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  have hcopF : Nat.Coprime (Fintype.card W) p := by
    rw [Fintype.card_eq_nat_card]; exact hcop
  obtain ⟨b, hb⟩ := hW
  let B : G → M := fun g => if hg : g ∈ W then b ⟨g, hg⟩ else 0
  have hB : ∀ w : W, B (w : G) = b w := fun w => dif_pos w.2
  let E₀ : G → G → M := fun g h => c g h - dlt B g h
  have hE₀coc : SSGRoute.IsCocycle2 (MonoidHom.id G) E₀ := coc_sub hc (dlt_cocycle B)
  have hE₀ : ∀ g h l : G, g • E₀ h l - E₀ (g * h) l + E₀ g (h * l) - E₀ g h = 0 :=
    isCocycle2_id_iff.mp hE₀coc
  have hE₀W : ∀ w w' : W, E₀ (w : G) (w' : G) = 0 := by
    intro w w'
    have h1 : E₀ (w : G) (w' : G) = c (w : G) (w' : G) - ((w : G) • b w' - b (w * w') + b w) := by
      show c (w : G) (w' : G) - dlt B (w : G) (w' : G)
        = c (w : G) (w' : G) - ((w : G) • b w' - b (w * w') + b w)
      rw [dlt, show ((w : G) * (w' : G)) = ((w * w' : W) : G) from rfl]
      simp only [hB]
    rw [h1, hb w w']; abel
  -- the first averaging `θ`, killing the `W`-dependence in the *second* variable
  let N : ℕ := Fintype.card W
  have hNne : (((N : ℕ) : ZMod p)) ≠ 0 := by
    have hunit : IsUnit (((N : ℕ) : ZMod p)) := (ZMod.isUnit_iff_coprime N p).mpr hcopF
    exact hunit.ne_zero
  let θ : G → M := fun g => (((N : ℕ) : ZMod p))⁻¹ • ∑ u : W, E₀ g (u : G)
  have hθW : ∀ w : W, θ (w : G) = 0 := by
    intro w
    show (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₀ (w : G) (u : G)) = 0
    rw [Finset.sum_eq_zero (fun u _ => hE₀W w u), smul_zero]
  have hθdiff : ∀ (g : G) (w : W), θ g - θ (g * (w : G)) = E₀ g (w : G) := by
    intro g w
    have h2 : ∀ u : W, E₀ (g * (w : G)) (u : G) = E₀ g ((w : G) * (u : G)) - E₀ g (w : G) := by
      intro u
      have hh := hE₀ g (w : G) (u : G)
      rw [hE₀W w u, smul_zero] at hh
      have hb' := solve_b hh
      rwa [zero_add] at hb'
    have hterm : ∀ u : W, E₀ g (u : G) - E₀ (g * (w : G)) (u : G)
        = E₀ g (u : G) - E₀ g ((w : G) * (u : G)) + E₀ g (w : G) := by
      intro u; rw [h2 u]; abel
    have hreindex : (∑ u : W, E₀ g ((w : G) * (u : G))) = ∑ u : W, E₀ g (u : G) := by
      have hcoe : (∑ u : W, E₀ g ((w : G) * (u : G))) = ∑ u : W, E₀ g (((w * u : W) : G)) :=
        Finset.sum_congr rfl (fun u _ => by rw [Subgroup.coe_mul])
      rw [hcoe]
      exact Equiv.sum_comp (Equiv.mulLeft w) (fun v : W => E₀ g (v : G))
    have hmain : (∑ u : W, E₀ g (u : G)) - (∑ u : W, E₀ (g * (w : G)) (u : G))
        = ((N : ℕ) : ZMod p) • E₀ g (w : G) := by
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl (fun u _ => hterm u)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hreindex]
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
      abel
    show (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₀ g (u : G))
        - (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₀ (g * (w : G)) (u : G)) = E₀ g (w : G)
    rw [← smul_sub, hmain, smul_smul, inv_mul_cancel₀ hNne, one_smul]
  let E₁ : G → G → M := fun g h => E₀ g h - dlt θ g h
  have hE₁coc : SSGRoute.IsCocycle2 (MonoidHom.id G) E₁ := coc_sub hE₀coc (dlt_cocycle θ)
  have hE₁ : ∀ g h l : G, g • E₁ h l - E₁ (g * h) l + E₁ g (h * l) - E₁ g h = 0 :=
    isCocycle2_id_iff.mp hE₁coc
  have hE₁W : ∀ g : G, ∀ w : W, E₁ g (w : G) = 0 := by
    intro g w
    have h1 : dlt θ g (w : G) = E₀ g (w : G) := by
      rw [dlt, hθW w, smul_zero]
      have h2 : (0 : M) - θ (g * (w : G)) + θ g = θ g - θ (g * (w : G)) := by abel
      rw [h2, hθdiff g w]
    show E₀ g (w : G) - dlt θ g (w : G) = 0
    rw [h1, sub_self]
  have hE₁invR : ∀ g h : G, ∀ w : W, E₁ g (h * (w : G)) = E₁ g h := by
    intro g h w
    have hh := hE₁ g h (w : G)
    rw [hE₁W h w, smul_zero, hE₁W (g * h) w] at hh
    have := solve_cc hh
    simpa using this
  have hE₁invL2 : ∀ (g : G) (w : W) (h : G), E₁ g ((w : G) * h) = E₁ g h := by
    intro g w h
    have hconj : h⁻¹ * (w : G) * h ∈ W := by
      have hx := Subgroup.Normal.conj_mem (inferInstance : W.Normal) (w : G) w.2 h⁻¹
      simpa [mul_assoc] using hx
    have hww : ((w : G) * h) = h * ((⟨h⁻¹ * (w : G) * h, hconj⟩ : W) : G) := by
      show (w : G) * h = h * (h⁻¹ * (w : G) * h); group
    rw [hww, hE₁invR g h ⟨h⁻¹ * (w : G) * h, hconj⟩]
  have hcross : ∀ (h : G) (a b : W),
      E₁ ((a * b : W) : G) h = (a : G) • E₁ (b : G) h + E₁ (a : G) h := by
    intro h a b
    have hh := hE₁ (a : G) (b : G) h
    rw [hE₁W a b, hE₁invL2 (a : G) b h, show ((a : G) * (b : G)) = ((a * b : W) : G) from rfl] at hh
    have := solve_b hh
    rw [sub_zero] at this
    exact this
  -- the second averaging `γ`, killing the `W`-dependence in the *first* variable
  let γ : G → M := fun h => - ( (((N : ℕ) : ZMod p))⁻¹ • ∑ u : W, E₁ (u : G) h )
  let E₂ : G → G → M := fun g h => E₁ g h - dlt γ g h
  have hE₂coc : SSGRoute.IsCocycle2 (MonoidHom.id G) E₂ := coc_sub hE₁coc (dlt_cocycle γ)
  have hE₂ : ∀ g h l : G, g • E₂ h l - E₂ (g * h) l + E₂ g (h * l) - E₂ g h = 0 :=
    isCocycle2_id_iff.mp hE₂coc
  have hγW : ∀ w : W, γ (w : G) = 0 := by
    intro w
    show - ( (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₁ (u : G) (w : G)) ) = 0
    simp only [hE₁W, Finset.sum_const_zero, smul_zero, neg_zero]
  have hγright : ∀ (g : G) (w : W), γ (g * (w : G)) = γ g := by
    intro g w
    have hsum : (∑ u : W, E₁ (u : G) (g * (w : G))) = ∑ u : W, E₁ (u : G) g :=
      Finset.sum_congr rfl (fun u _ => hE₁invR (u : G) g w)
    show - ( (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₁ (u : G) (g * (w : G))) )
      = - ( (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₁ (u : G) g) )
    rw [hsum]
  have hγleft : ∀ (h : G) (w : W), γ ((w : G) * h) = γ h := by
    intro h w
    have hsum : (∑ u : W, E₁ (u : G) ((w : G) * h)) = ∑ u : W, E₁ (u : G) h :=
      Finset.sum_congr rfl (fun u _ => hE₁invL2 (u : G) w h)
    show - ( (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₁ (u : G) ((w : G) * h)) )
      = - ( (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₁ (u : G) h) )
    rw [hsum]
  have hTate : ∀ (h : G) (w : W), E₁ (w : G) h = (w : G) • γ h - γ h := by
    intro h w
    have hf : ∀ a b : W, (fun u : W => E₁ (u : G) h) (a * b)
        = a • (fun u : W => E₁ (u : G) h) b + (fun u : W => E₁ (u : G) h) a := by
      intro a b
      show E₁ ((a * b : W) : G) h = (a : G) • E₁ (b : G) h + E₁ (a : G) h
      exact hcross h a b
    obtain ⟨gm, hgmdef, hgm⟩ := crossed_hom_average hcopF (fun u : W => E₁ (u : G) h) hf
    have hγeq : γ h = gm := by rw [hgmdef]
    rw [hγeq]
    exact hgm w
  have hE₂vanR : ∀ (g : G) (w : W), E₂ g (w : G) = 0 := by
    intro g w
    have h1 : dlt γ g (w : G) = 0 := by
      rw [dlt, hγW w, smul_zero, hγright g w]; abel
    show E₁ g (w : G) - dlt γ g (w : G) = 0
    rw [hE₁W g w, h1, sub_zero]
  have hE₂vanL : ∀ (h : G) (w : W), E₂ (w : G) h = 0 := by
    intro h w
    have h1 : dlt γ (w : G) h = E₁ (w : G) h := by
      rw [dlt, hγW w, hγleft h w, hTate h w]; abel
    show E₁ (w : G) h - dlt γ (w : G) h = 0
    rw [h1, sub_self]
  have hE₂invR : ∀ (g h : G) (w : W), E₂ g (h * (w : G)) = E₂ g h := by
    intro g h w
    have h1 : dlt γ g (h * (w : G)) = dlt γ g h := by
      have harg2 : γ (h * (w : G)) = γ h := hγright h w
      have harg : γ (g * (h * (w : G))) = γ (g * h) := by
        rw [← mul_assoc, hγright (g * h) w]
      rw [dlt, dlt, harg2, harg]
    show E₁ g (h * (w : G)) - dlt γ g (h * (w : G)) = E₁ g h - dlt γ g h
    rw [hE₁invR g h w, h1]
  have hE₂invL2 : ∀ (g : G) (w : W) (h : G), E₂ g ((w : G) * h) = E₂ g h := by
    intro g w h
    have hconj : h⁻¹ * (w : G) * h ∈ W := by
      have hx := Subgroup.Normal.conj_mem (inferInstance : W.Normal) (w : G) w.2 h⁻¹
      simpa [mul_assoc] using hx
    have hww : ((w : G) * h) = h * ((⟨h⁻¹ * (w : G) * h, hconj⟩ : W) : G) := by
      show (w : G) * h = h * (h⁻¹ * (w : G) * h); group
    rw [hww, hE₂invR g h ⟨h⁻¹ * (w : G) * h, hconj⟩]
  have hE₂invR1 : ∀ (g : G) (w : W) (h : G), E₂ (g * (w : G)) h = E₂ g h := by
    intro g w h
    have hh := hE₂ g (w : G) h
    rw [hE₂vanL h w, hE₂vanR g w, hE₂invL2 g w h] at hh
    have := solve_b hh
    simpa using this
  have hE₂fix : ∀ (g h : G) (w : W), (w : G) • E₂ g h = E₂ g h := by
    intro g h w
    have hh := hE₂ (w : G) g h
    rw [hE₂vanL (g * h) w, hE₂vanL g w] at hh
    have hcong : E₂ ((w : G) * g) h = E₂ g h := by
      have hconj : g⁻¹ * (w : G) * g ∈ W := by
        have hx := Subgroup.Normal.conj_mem (inferInstance : W.Normal) (w : G) w.2 g⁻¹
        simpa [mul_assoc] using hx
      have hww : ((w : G) * g) = g * ((⟨g⁻¹ * (w : G) * g, hconj⟩ : W) : G) := by
        show (w : G) * g = g * (g⁻¹ * (w : G) * g); group
      rw [hww, hE₂invR1 g ⟨g⁻¹ * (w : G) * g, hconj⟩ h]
    have ha := solve_a hh
    rw [hcong] at ha
    simpa using ha
  -- the descended cocycle on `G ⧸ W`
  let c₀ : G ⧸ W → G ⧸ W → M := fun x y => E₂ (Quotient.out x) (Quotient.out y)
  have hc₀ : ∀ g h : G, c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W h) = E₂ g h := by
    intro g h
    have hg : ∃ z ∈ W, g * z = Quotient.out (QuotientGroup.mk' W g) := by
      refine (QuotientGroup.mk'_eq_mk' W).mp ?_
      conv_rhs => rw [QuotientGroup.mk'_apply, QuotientGroup.out_eq']
    have hh : ∃ z ∈ W, h * z = Quotient.out (QuotientGroup.mk' W h) := by
      refine (QuotientGroup.mk'_eq_mk' W).mp ?_
      conv_rhs => rw [QuotientGroup.mk'_apply, QuotientGroup.out_eq']
    obtain ⟨z, hzW, hgz⟩ := hg
    obtain ⟨z', hz'W, hgz'⟩ := hh
    show E₂ (Quotient.out (QuotientGroup.mk' W g)) (Quotient.out (QuotientGroup.mk' W h)) = E₂ g h
    rw [← hgz, ← hgz', hE₂invR (g * z) h ⟨z', hz'W⟩, hE₂invR1 g ⟨z, hzW⟩ h]
  refine ⟨B + θ + γ, c₀, ?_, ?_, ?_⟩
  · intro g h l
    rw [hc₀ h l, hc₀ (g * h) l, hc₀ g (h * l), hc₀ g h]
    exact hE₂ g h l
  · intro g h w
    rw [hc₀ g h]
    exact hE₂fix g h w
  · intro g h
    rw [hc₀ g h]
    show c g h = dlt (B + θ + γ) g h + E₂ g h
    have hdl : dlt (B + θ + γ) g h = dlt B g h + dlt θ g h + dlt γ g h := by
      rw [dlt_add, dlt_add]
    have h0 : E₀ g h = c g h - dlt B g h := rfl
    have h1 : E₁ g h = E₀ g h - dlt θ g h := rfl
    have h2 : E₂ g h = E₁ g h - dlt γ g h := rfl
    rw [hdl, h2, h1, h0]; abel

end Work.SSGRoute
