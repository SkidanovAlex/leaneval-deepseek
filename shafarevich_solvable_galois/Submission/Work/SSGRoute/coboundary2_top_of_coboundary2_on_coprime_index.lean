import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Coprime-index restriction for continuous `H²`

A continuous (`IsLocConst2`) `2`-cocycle `c : Γ × Γ → M` on a compact topological group `Γ`,
with values in a finite `𝔽_p`-module `M` on which `Γ` acts through `act : Γ →* G`, which is a
coboundary on a *normal closed* subgroup `H ≤ Γ` of index coprime to `p`, is a coboundary on `Γ`.

The proof is the "inflation is zero" transfer argument, carried out at the level of cochains so
that the primitive can be made locally constant:

* choose an open normal subgroup `V ≤ H` on which both `c` and the primitive `b` of `c|_H` are
  invariant; then `c` and `b` take values in the fixed points `M^V` and are invariant under right
  multiplication by `V`;
* extend `b` to a cochain `btil` on `Γ` satisfying the *normalised* relation
  `c σ h = act σ • btil h - btil (σ*h) + btil σ` for all `σ : Γ`, `h ∈ H` (transversal
  construction), and check that `btil` is `V`-invariant;
* the cocycle `u := c - d btil` then vanishes on `Γ × H`, is right-`H`-invariant in the second
  variable and right-`V`-invariant in the first; averaging `u` over the coset space `Γ ⧸ H` and
  dividing by the (invertible) index `[Γ : H]` produces a primitive `B` of `u` which is again
  `V`-invariant;
* `btil + B` is the required locally constant primitive of `c`.
-/

namespace Work.SSGRoute

open scoped Pointwise

/-! ## The twisted differential -/

section TwistedDifferential

variable {Γ : Type} [Group Γ] {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- The twisted `1`-coboundary of a `1`-cochain. -/
def cob2d (act : Γ →* G) (b : Γ → M) (σ τ : Γ) : M := act σ • b τ - b (σ * τ) + b σ

/-- The twisted differential of a `1`-cochain is a `2`-cocycle. -/
lemma cob2d_isCocycle (act : Γ →* G) (b : Γ → M) : SSGRoute.IsCocycle2 act (cob2d act b) := by
  intro g h l
  simp only [cob2d, map_mul, mul_assoc, mul_smul, smul_sub, smul_add]
  abel

/-- The difference of two `2`-cocycles is a `2`-cocycle. -/
lemma cob2_isCocycle2_sub {act : Γ →* G} {c c' : Γ → Γ → M}
    (hc : SSGRoute.IsCocycle2 act c) (hc' : SSGRoute.IsCocycle2 act c') :
    SSGRoute.IsCocycle2 act (fun g h => c g h - c' g h) := by
  intro g h l
  have h1 := hc g h l
  have h2 := hc' g h l
  have key : act g • (c h l - c' h l) - (c (g * h) l - c' (g * h) l)
      + (c g (h * l) - c' g (h * l)) - (c g h - c' g h)
      = (act g • c h l - c (g * h) l + c g (h * l) - c g h)
        - (act g • c' h l - c' (g * h) l + c' g (h * l) - c' g h) := by
    rw [smul_sub]
    abel
  rw [key, h1, h2, sub_zero]

/-- From `a - b + c - d = 0` conclude `c = d - a + b`. -/
lemma cob2_solve {a b c d : M} (h : a - b + c - d = 0) : c = d - a + b := by
  have h' : a - b + c = d := sub_eq_zero.mp h
  rw [← h']
  abel

/-- From `a - b + c - d = 0` conclude `b = a + c - d`. -/
lemma cob2_solve2 {a b c d : M} (h : a - b + c - d = 0) : b = a + c - d := by
  have h2 : a - b + c = d := sub_eq_zero.mp h
  have h' : a + c = d + b := by rw [← h2]; abel
  rw [eq_sub_iff_add_eq, add_comm b d, h']

/-- From `a - b + c - d = 0` conclude `a = d - c + b`. -/
lemma cob2_solve3 {a b c d : M} (h : a - b + c - d = 0) : a = d - c + b := by
  have h' : a - b + c = d := sub_eq_zero.mp h
  rw [← h']
  abel

/-- From `a - b + c - d = 0` conclude `d = a - b + c`. -/
lemma cob2_solve4 {a b c d : M} (h : a - b + c - d = 0) : d = a - b + c :=
  (sub_eq_zero.mp h).symm

/-- The action of a group element is injective on additive coefficients. -/
lemma cob2_smul_eq_zero {g : G} {m : M} (h : g • m = 0) : m = 0 := by
  have h2 : g⁻¹ • (g • m) = g⁻¹ • (0 : M) := congrArg _ h
  rw [← mul_smul, inv_mul_cancel, one_smul, smul_zero] at h2
  exact h2

end TwistedDifferential

/-! ## Extending a primitive along a transversal -/

section PrimitiveExtension

variable {Γ : Type} [Group Γ] {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- Decomposition of `x` along the transversal of the cosets of `H`: `x = r x * k x` with
`r x = Quotient.out (mk x)` and `k x ∈ H`. -/
lemma cob2_exists_decomp (H : Subgroup Γ) [H.Normal] (x : Γ) :
    ∃ h ∈ H, x = Quotient.out (QuotientGroup.mk' H x) * h := by
  refine ⟨(Quotient.out (QuotientGroup.mk' H x))⁻¹ * x, ?_, by group⟩
  rw [← QuotientGroup.eq_one_iff (N := H)]
  show QuotientGroup.mk' H ((Quotient.out (QuotientGroup.mk' H x))⁻¹ * x) = 1
  rw [map_mul, map_inv, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.out_eq',
    inv_mul_cancel]

/-- **Extending a primitive from `H` to `Γ`.**

Let `c : Γ → Γ → M` be a twisted `2`-cocycle (`hc`), let `b : Γ → M` be a primitive for `c` on a
subgroup `H ≤ Γ` (`hb`), and let `V ≤ H` be a subgroup such that `b` is invariant under right
multiplication by `V` on `H` (`hlocb`), `c` is invariant under right multiplication by `V` in both
variables (`hlocc`) and both `c` and `b|_H` take values in the `V`-fixed points (`hcN`, `hbN`).
Then `c` admits a primitive `btil : Γ → M` which agrees with `b` on `H`, satisfies the normalised
relation `c σ h = act σ • btil h - btil (σ*h) + btil σ` for *every* `σ : Γ` and `h ∈ H`, is
invariant under right multiplication by `V`, and takes values in the `V`-fixed points. -/
theorem cob2_exists_primitive_extension
    (act : Γ →* G) (H : Subgroup Γ) [H.Normal] (c : Γ → Γ → M) (b : Γ → M) (V : Subgroup Γ)
    [V.Normal]
    (hc : ∀ a b d : Γ, act a • c b d - c (a * b) d + c a (b * d) - c a b = 0)
    (hb : ∀ x ∈ H, ∀ y ∈ H, c x y = act x • b y - b (x * y) + b x)
    (hlocb : ∀ g ∈ H, ∀ u ∈ V, u ∈ H → b (g * u) = b g)
    (hlocc : ∀ g h u v : Γ, u ∈ V → v ∈ V → c (g * u) (h * v) = c g h)
    (hcN : ∀ σ τ : Γ, ∀ v ∈ V, act v • c σ τ = c σ τ)
    (hbN : ∀ h ∈ H, ∀ v ∈ V, act v • b h = b h) :
    ∃ btil : Γ → M, (∀ h ∈ H, btil h = b h) ∧
      (∀ σ : Γ, ∀ h ∈ H, c σ h = act σ • btil h - btil (σ * h) + btil σ) ∧
      (∀ σ v : Γ, v ∈ V → v ∈ H → btil (σ * v) = btil σ) ∧
      (∀ σ : Γ, ∀ v ∈ V, act v • btil σ = btil σ) := by
  classical
  let r : Γ → Γ := fun σ => Quotient.out (QuotientGroup.mk' H σ)
  let t₀ : Γ := Quotient.out (QuotientGroup.mk' H (1 : Γ))
  have ht₀_mem : t₀ ∈ H := by
    rw [← QuotientGroup.eq_one_iff (N := H)]
    show QuotientGroup.mk' H t₀ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.out_eq', map_one]
  have hdec : ∀ σ : Γ, ∃ h ∈ H, σ = r σ * h := by
    intro σ
    obtain ⟨h, hh, hσ⟩ := cob2_exists_decomp H σ
    exact ⟨h, hh, hσ⟩
  choose k hk_mem hk_spec using hdec
  have hr_mul : ∀ (σ v : Γ), v ∈ H → r (σ * v) = r σ := by
    intro σ v hv
    show Quotient.out (QuotientGroup.mk' H (σ * v)) = Quotient.out (QuotientGroup.mk' H σ)
    have hq : QuotientGroup.mk' H (σ * v) = QuotientGroup.mk' H σ := by
      rw [map_mul]
      have h1 : QuotientGroup.mk' H v = 1 := by
        simpa using (QuotientGroup.eq_one_iff (N := H) v).mpr hv
      rw [h1, mul_one]
    rw [hq]
  have hk_mul : ∀ (σ v : Γ), v ∈ H → k (σ * v) = k σ * v := by
    intro σ v hv
    apply mul_left_cancel (a := r (σ * v))
    rw [← hk_spec (σ * v), hr_mul σ v hv, ← mul_assoc, ← hk_spec σ]
  let Aa : Γ → M := fun t => if t = t₀ then b t₀ else 0
  let btil : Γ → M := fun σ => act (r σ) • b (k σ) - c (r σ) (k σ) + Aa (r σ)
  have hbtil_apply : ∀ σ : Γ, btil σ = act (r σ) • b (k σ) - c (r σ) (k σ) + Aa (r σ) :=
    fun σ => rfl
  -- agreement with `b` on `H`
  have hbtil_restrict : ∀ h ∈ H, btil h = b h := by
    intro h hh
    have hr_h : r h = t₀ := by
      show Quotient.out (QuotientGroup.mk' H h) = Quotient.out (QuotientGroup.mk' H (1 : Γ))
      have hq : QuotientGroup.mk' H h = QuotientGroup.mk' H (1 : Γ) := by
        have h1 : QuotientGroup.mk' H h = 1 := by
          simpa using (QuotientGroup.eq_one_iff (N := H) h).mpr hh
        rw [h1, map_one]
      rw [hq]
    have hk_h : k h = t₀⁻¹ * h := by
      apply mul_left_cancel (a := r h)
      rw [← hk_spec h, hr_h]
      group
    have hb1 : c t₀ (t₀⁻¹ * h) = act t₀ • b (t₀⁻¹ * h) - b h + b t₀ := by
      have := hb t₀ ht₀_mem (t₀⁻¹ * h) (H.mul_mem (H.inv_mem ht₀_mem) hh)
      rwa [show t₀ * (t₀⁻¹ * h) = h from by group] at this
    have hAa : Aa t₀ = b t₀ := by simp only [Aa, if_pos rfl]
    rw [hbtil_apply h, hr_h, hk_h, hAa, hb1]
    abel
  -- the normalised coboundary relation
  have hbtil_rec : ∀ σ : Γ, ∀ h ∈ H, c σ h = act σ • btil h - btil (σ * h) + btil σ := by
    intro σ h hh
    have hr := hr_mul σ h hh
    have hk := hk_mul σ h hh
    have h1 : b (k σ * h) = act (k σ) • b h - c (k σ) h + b (k σ) := by
      have := hb (k σ) (hk_mem σ) h hh
      rw [this]; abel
    have h2 := hc (r σ) (k σ) h
    have h3 : c σ h = act (r σ) • c (k σ) h + c (r σ) (k σ * h) - c (r σ) (k σ) := by
      have h4 := cob2_solve2 h2
      rw [← hk_spec σ] at h4
      exact h4
    have hact : act σ = act (r σ) * act (k σ) := by
      conv_lhs => rw [hk_spec σ]
      rw [map_mul]
    rw [hbtil_apply (σ * h), hr, hk, hbtil_apply σ, hbtil_restrict h hh, h1, h3, hact,
      mul_smul, smul_add, smul_sub]
    abel
  -- right-`V`-invariance
  have hbtil_loc : ∀ σ v : Γ, v ∈ V → v ∈ H → btil (σ * v) = btil σ := by
    intro σ v hv hvH
    have hcv : c (r σ) (k σ * v) = c (r σ) (k σ) := by
      have := hlocc (r σ) (k σ) 1 v (V.one_mem) hv
      rwa [mul_one] at this
    rw [hbtil_apply (σ * v), hr_mul σ v hvH, hk_mul σ v hvH, hbtil_apply σ,
      hlocb (k σ) (hk_mem σ) v hv hvH, hcv]
  -- values lie in the `V`-fixed points
  have hbtil_N : ∀ σ : Γ, ∀ v ∈ V, act v • btil σ = btil σ := by
    intro σ v hv
    have hconj : (r σ)⁻¹ * v * (r σ) ∈ V := by
      have hx := (inferInstance : V.Normal).conj_mem v hv (r σ)⁻¹
      simpa using hx
    have h1 : act v • (act (r σ) • b (k σ)) = act (r σ) • b (k σ) := by
      have hv1 : act v * act (r σ) = act (r σ) * act ((r σ)⁻¹ * v * (r σ)) := by
        rw [← map_mul, ← map_mul]
        congr 1
        group
      rw [← mul_smul, hv1, mul_smul, hbN (k σ) (hk_mem σ) ((r σ)⁻¹ * v * (r σ)) hconj]
    have h2 : act v • c (r σ) (k σ) = c (r σ) (k σ) := hcN (r σ) (k σ) v hv
    have h3 : act v • Aa (r σ) = Aa (r σ) := by
      show act v • (if r σ = t₀ then b t₀ else 0) = (if r σ = t₀ then b t₀ else 0)
      by_cases hr : r σ = t₀
      · rw [if_pos hr]
        exact hbN t₀ ht₀_mem v hv
      · rw [if_neg hr]
        simp
    rw [hbtil_apply σ, smul_add, smul_sub, h1, h2, h3]
  exact ⟨btil, hbtil_restrict, hbtil_rec, hbtil_loc, hbtil_N⟩

end PrimitiveExtension

/-! ## Averaging a cocycle over the quotient `Γ ⧸ H` -/

section QuotientAverage

/-- **Averaging a `2`-cocycle over the coset space.**

Let `H ⊴ Γ` be a normal subgroup of finite index `n = H.index` coprime to `p` and let `M` be a
module over `ZMod p` with an action of `Γ` through `act : Γ →* G`, commuting with the scalars.  If
`u : Γ → Γ → M` is a twisted `2`-cocycle which is right-`H`-invariant in the second variable and
right-`V`-invariant in the first variable, then `u` is a coboundary, with a primitive `B` which is
itself right-`V`-invariant.

The primitive is `B(σ) = (1/n) · Σ_{q ∈ Γ ⧸ H} u σ (sec q)`: the cocycle identity turns
`d B(σ,τ)` into `n • u σ τ + Σ_q u σ (sec q) - Σ_q u σ (τ · sec q)`, and the two sums cancel
because `q ↦ (mk τ) * q` permutes the coset space. -/
theorem cob2_average
    (p : ℕ) [Fact p.Prime] {Γ : Type} [Group Γ]
    {G M : Type} [Group G] [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) [H.Normal] [H.FiniteIndex]
    (hcop : Nat.Coprime H.index p) (V : Subgroup Γ) (u : Γ → Γ → M)
    (hcoc : ∀ a b c : Γ, act a • u b c - u (a * b) c + u a (b * c) - u a b = 0)
    (hinv2 : ∀ a b : Γ, ∀ h ∈ H, u a (b * h) = u a b)
    (hinv1 : ∀ a b : Γ, ∀ h ∈ V, u (a * h) b = u a b) :
    ∃ B : Γ → M, (∀ σ : Γ, ∀ v ∈ V, B (σ * v) = B σ) ∧
      ∀ σ τ : Γ, act σ • B τ - B (σ * τ) + B σ = u σ τ := by
  classical
  letI : Fintype (Γ ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex (H := H)
  let n : ℕ := H.index
  have hcard : Fintype.card (Γ ⧸ H) = n := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index_eq_card]
  let C : Γ → M := fun σ => ∑ q : Γ ⧸ H, u σ (Quotient.out q)
  have hC : ∀ σ τ : Γ, act σ • C τ - C (σ * τ) + C σ = n • u σ τ := by
    intro σ τ
    have hterm : ∀ q : Γ ⧸ H,
        act σ • u τ (Quotient.out q) - u (σ * τ) (Quotient.out q) + u σ (Quotient.out q)
          = u σ τ + u σ (Quotient.out q) - u σ (τ * Quotient.out q) := by
      intro q
      have h := hcoc σ τ (Quotient.out q)
      have h' := cob2_solve4 h
      rw [h']
      abel
    have hsum : act σ • C τ - C (σ * τ) + C σ
        = (∑ q : Γ ⧸ H, u σ τ) + (∑ q : Γ ⧸ H, u σ (Quotient.out q))
          - (∑ q : Γ ⧸ H, u σ (τ * Quotient.out q)) := by
      have hL : act σ • C τ - C (σ * τ) + C σ
          = ∑ q : Γ ⧸ H, (act σ • u τ (Quotient.out q) - u (σ * τ) (Quotient.out q)
              + u σ (Quotient.out q)) := by
        show act σ • (∑ q : Γ ⧸ H, u τ (Quotient.out q))
            - (∑ q : Γ ⧸ H, u (σ * τ) (Quotient.out q))
            + (∑ q : Γ ⧸ H, u σ (Quotient.out q)) = _
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      have hR : (∑ q : Γ ⧸ H, u σ τ) + (∑ q : Γ ⧸ H, u σ (Quotient.out q))
          - (∑ q : Γ ⧸ H, u σ (τ * Quotient.out q))
          = ∑ q : Γ ⧸ H, (u σ τ + u σ (Quotient.out q) - u σ (τ * Quotient.out q)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      rw [hL, hR]
      exact Finset.sum_congr rfl fun q _ => hterm q
    have hperm : (∑ q : Γ ⧸ H, u σ (τ * Quotient.out q))
        = ∑ q : Γ ⧸ H, u σ (Quotient.out q) := by
      have h1 : ∀ q : Γ ⧸ H, u σ (τ * Quotient.out q)
          = u σ (Quotient.out (QuotientGroup.mk' H τ * q)) := by
        intro q
        obtain ⟨h, hh, hx⟩ := cob2_exists_decomp H (τ * Quotient.out q)
        have hq : QuotientGroup.mk' H (τ * Quotient.out q) = QuotientGroup.mk' H τ * q := by
          rw [map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.out_eq']
        rw [hx, hinv2 σ (Quotient.out (QuotientGroup.mk' H (τ * Quotient.out q))) h hh, hq]
      rw [Finset.sum_congr rfl fun q _ => h1 q]
      exact Equiv.sum_comp (Equiv.mulLeft (QuotientGroup.mk' H τ))
        (fun q => u σ (Quotient.out q))
    rw [hsum, hperm]
    simp only [Finset.sum_const, Finset.card_univ, hcard]
    abel
  have hn_ne : (((n : ℕ)) : ZMod p) ≠ 0 := by
    have hcop' : Nat.Coprime n p := by simpa [n] using hcop
    exact (ZMod.isUnit_iff_coprime n p).mpr hcop' |>.ne_zero
  refine ⟨fun σ => (((n : ℕ) : ZMod p))⁻¹ • C σ, ?_, ?_⟩
  · intro σ v hv
    show (((n : ℕ) : ZMod p))⁻¹ • C (σ * v) = (((n : ℕ) : ZMod p))⁻¹ • C σ
    congr 1
    exact Finset.sum_congr rfl fun q _ => hinv1 σ (Quotient.out q) v hv
  · intro σ τ
    show act σ • ((((n : ℕ) : ZMod p))⁻¹ • C τ) - (((n : ℕ) : ZMod p))⁻¹ • C (σ * τ)
        + (((n : ℕ) : ZMod p))⁻¹ • C σ = u σ τ
    rw [smul_comm (act σ) (((n : ℕ) : ZMod p))⁻¹ (C τ), ← smul_sub, ← smul_add, hC σ τ,
      ← Nat.cast_smul_eq_nsmul (ZMod p) n (u σ τ), smul_smul]
    have hninv : (((n : ℕ) : ZMod p))⁻¹ * ((n : ℕ) : ZMod p) = 1 := inv_mul_cancel₀ hn_ne
    rw [hninv, one_smul]

end QuotientAverage

/-! ## The main theorem -/

theorem coboundary2_top_of_coboundary2_on_coprime_index
    (p : ℕ) [Fact p.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {G M : Type} [Group G] [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] [Finite M]
    (act : Γ →* G) (H : Subgroup Γ) (hH : H.Normal) (hcl : IsClosed (H : Set Γ))
    (hfin : H.FiniteIndex) (hcop : Nat.Coprime H.index p)
    (c : Γ → Γ → M) (hc : SSGRoute.IsCocycle2 act c) (hlc : SSGRoute.IsLocConst2 c)
    (h : SSGRoute.IsCoboundary2On act H c) :
    SSGRoute.IsCoboundary2On act ⊤ c := by
  classical
  haveI hHN : H.Normal := hH
  haveI hHF : H.FiniteIndex := hfin
  obtain ⟨b, hb_loc, hb_eq⟩ := h
  obtain ⟨Ub, hUb_open, hUb⟩ := hb_loc
  obtain ⟨Uc, hUc_open, hUc⟩ := hlc
  have hHopen : IsOpen (H : Set Γ) := Subgroup.isOpen_of_isClosed_of_finiteIndex H hcl
  -- an open normal subgroup `V ≤ H` of invariance for `c` and `b`
  let V : Subgroup Γ := Ub.normalCore ⊓ Uc.normalCore ⊓ H
  have hV_le_Ub : V ≤ Ub := fun x hx => Ub.normalCore_le hx.1.1
  have hV_le_Uc : V ≤ Uc := fun x hx => Uc.normalCore_le hx.1.2
  have hV_le_H : V ≤ H := fun x hx => hx.2
  have hVconj : ∀ (g v : Γ), v ∈ V → g⁻¹ * v * g ∈ V := by
    intro g v hv
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hx := Ub.normalCore_normal.conj_mem v hv.1.1 g⁻¹
      simpa using hx
    · have hx := Uc.normalCore_normal.conj_mem v hv.1.2 g⁻¹
      simpa using hx
    · have hx := hHN.conj_mem v hv.2 g⁻¹
      simpa using hx
  haveI hVnorm : V.Normal := ⟨fun n hn g => by
    have := hVconj g⁻¹ n hn
    simpa using this⟩
  have hV_open : IsOpen (V : Set Γ) := by
    have hfinUb : Ub.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff_finite_quotient]
      haveI : DiscreteTopology (Γ ⧸ Ub) := QuotientGroup.discreteTopology_iff.mpr hUb_open
      exact finite_of_compact_of_discrete
    have hfinUc : Uc.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff_finite_quotient]
      haveI : DiscreteTopology (Γ ⧸ Uc) := QuotientGroup.discreteTopology_iff.mpr hUc_open
      exact finite_of_compact_of_discrete
    have h1 : IsOpen ((Ub.normalCore : Subgroup Γ) : Set Γ) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _
        (Subgroup.normalCore_isClosed Ub (Subgroup.isClosed_of_isOpen Ub hUb_open))
    have h2 : IsOpen ((Uc.normalCore : Subgroup Γ) : Set Γ) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _
        (Subgroup.normalCore_isClosed Uc (Subgroup.isClosed_of_isOpen Uc hUc_open))
    show IsOpen (((Ub.normalCore ⊓ Uc.normalCore ⊓ H : Subgroup Γ)) : Set Γ)
    rw [Subgroup.coe_inf, Subgroup.coe_inf]
    exact (h1.inter h2).inter hHopen
  -- `c` takes values in the `V`-fixed points
  have hcN : ∀ σ τ : Γ, ∀ v ∈ V, act v • c σ τ = c σ τ := by
    intro σ τ v hv
    -- the function `x ↦ c v x` is constant
    have hstep : ∀ (a x : Γ), act a • c v x = c a 1 := by
      intro a x
      have h1 : c (a * v) x = c a x := by
        have hx := hUc a x v 1 (hV_le_Uc hv) Uc.one_mem
        rwa [mul_one] at hx
      have h2 : c a (v * x) = c a x := by
        have hx := hUc a x 1 (x⁻¹ * v * x) Uc.one_mem (hV_le_Uc (hVconj x v hv))
        rw [show a * 1 = a from mul_one a,
          show x * (x⁻¹ * v * x) = v * x from by group] at hx
        exact hx
      have h3 : c a v = c a 1 := by
        have hx := hUc a 1 1 v Uc.one_mem (hV_le_Uc hv)
        rw [mul_one, one_mul] at hx
        exact hx
      have h4 := hc a v x
      rw [h1, h2, h3] at h4
      have key : act a • c v x - c a x + c a x - c a 1 = act a • c v x - c a 1 := by abel
      rw [key] at h4
      exact sub_eq_zero.mp h4
    have hconst : ∀ x : Γ, c v x = c v 1 := by
      intro x
      have h1 := hstep σ x
      have h2 := hstep σ 1
      have h3 : act σ • (c v x - c v 1) = 0 := by rw [smul_sub, h1, h2, sub_self]
      exact sub_eq_zero.mp (cob2_smul_eq_zero h3)
    have h6 : c (v * σ) τ = c σ τ := by
      have hx := hUc σ τ (σ⁻¹ * v * σ) 1 (hV_le_Uc (hVconj σ v hv)) Uc.one_mem
      rw [show σ * (σ⁻¹ * v * σ) = v * σ from by group, mul_one] at hx
      exact hx
    have h5 := hc v σ τ
    rw [h6, hconst (σ * τ), hconst σ] at h5
    have key : act v • c σ τ - c σ τ + c v 1 - c v 1 = act v • c σ τ - c σ τ := by abel
    rw [key] at h5
    exact sub_eq_zero.mp h5
  -- `b` takes values in the `V`-fixed points
  have hbN : ∀ h ∈ H, ∀ v ∈ V, act v • b h = b h := by
    intro h hh v hv
    have hvH : v ∈ H := hV_le_H hv
    have h1 : c (h * v) (h * v) = c h h := hUc h h v v (hV_le_Uc hv) (hV_le_Uc hv)
    have e1 : c (h * v) (h * v) = act (h * v) • b (h * v) - b (h * v * (h * v)) + b (h * v) :=
      hb_eq (h * v) (H.mul_mem hh hvH) (h * v) (H.mul_mem hh hvH)
    have e2 : c h h = act h • b h - b (h * h) + b h := hb_eq h hh h hh
    have bv1 : b (h * v) = b h := hUb h hh v (hV_le_Ub hv) hvH
    have bv2 : b (h * v * (h * v)) = b (h * h) := by
      have hconj : h⁻¹ * v * h ∈ V := hVconj h v hv
      have hw : (h⁻¹ * v * h) * v ∈ V := V.mul_mem hconj hv
      have hwH : (h⁻¹ * v * h) * v ∈ H := hV_le_H hw
      have hx := hUb (h * h) (H.mul_mem hh hh) ((h⁻¹ * v * h) * v) (hV_le_Ub hw) hwH
      rwa [show h * h * ((h⁻¹ * v * h) * v) = h * v * (h * v) from by group] at hx
    have A : act (h * v) • b (h * v) - b (h * v * (h * v)) + b (h * v)
        = act h • b h - b (h * h) + b h := by rw [← e1, h1, e2]
    have B : act (h * v) • b (h * v) = act h • (act v • b h) := by
      rw [map_mul, mul_smul, bv1]
    have C : act h • (act v • b h) - b (h * h) + b h = act h • b h - b (h * h) + b h := by
      have hkey : act (h * v) • b (h * v) - b (h * v * (h * v)) + b (h * v)
          = act h • (act v • b h) - b (h * h) + b h := by
        rw [B, bv1, bv2]
      rw [← hkey]
      exact A
    have C2 : act h • (act v • b h) = act h • b h := by
      have key : (act h • (act v • b h) - b (h * h) + b h)
          - (act h • b h - b (h * h) + b h) = 0 := by rw [C, sub_self]
      have hzero : (act h • (act v • b h) - b (h * h) + b h)
          - (act h • b h - b (h * h) + b h) = act h • (act v • b h) - act h • b h := by abel
      rw [hzero] at key
      exact sub_eq_zero.mp key
    have C3 : act h • (act v • b h - b h) = 0 := by rw [smul_sub, C2, sub_self]
    exact sub_eq_zero.mp (cob2_smul_eq_zero C3)
  -- extend `b` to `Γ`
  obtain ⟨btil, _hbtil_H, hbtil_rec, hbtil_loc, hbtil_N⟩ :=
    cob2_exists_primitive_extension act H c b V hc hb_eq
      (fun g hg u hu huH => hUb g hg u (hV_le_Ub hu) huH)
      (fun g h u v hu hv => hUc g h u v (hV_le_Uc hu) (hV_le_Uc hv)) hcN hbN
  let u : Γ → Γ → M := fun σ τ => c σ τ - (act σ • btil τ - btil (σ * τ) + btil σ)
  have hu_coc : ∀ a b d : Γ, act a • u b d - u (a * b) d + u a (b * d) - u a b = 0 :=
    cob2_isCocycle2_sub hc (cob2d_isCocycle act btil)
  have hu_H : ∀ σ : Γ, ∀ h ∈ H, u σ h = 0 := by
    intro σ h hh
    have hx := hbtil_rec σ h hh
    show c σ h - (act σ • btil h - btil (σ * h) + btil σ) = 0
    rw [hx]; abel
  have hu_inv2 : ∀ a b : Γ, ∀ h ∈ H, u a (b * h) = u a b := by
    intro a b h hh
    have h1 := hu_coc a b h
    rw [hu_H b h hh, hu_H (a * b) h hh] at h1
    simpa only [smul_zero, sub_zero, add_zero] using cob2_solve h1
  have hu_inv1 : ∀ a b : Γ, ∀ v ∈ V, u (a * v) b = u a b := by
    intro a b v hv
    have hvH : v ∈ H := hV_le_H hv
    have h1 : btil (a * v) = btil a := hbtil_loc a v hv hvH
    have h2 : act v • btil b = btil b := hbtil_N b v hv
    have h3 : btil (a * v * b) = btil (a * b) := by
      have hconj : b⁻¹ * v * b ∈ V := hVconj b v hv
      have hx := hbtil_loc (a * b) (b⁻¹ * v * b) hconj (hV_le_H hconj)
      rwa [show a * b * (b⁻¹ * v * b) = a * v * b from by group] at hx
    have h4 : c (a * v) b = c a b := by
      have hx := hUc a b v 1 (hV_le_Uc hv) Uc.one_mem
      rwa [mul_one] at hx
    show c (a * v) b - (act (a * v) • btil b - btil (a * v * b) + btil (a * v))
        = c a b - (act a • btil b - btil (a * b) + btil a)
    rw [h1, h3, h4, map_mul, mul_smul, h2]
  obtain ⟨B, hB_inv, hB_eq⟩ := cob2_average p act H hcop V u hu_coc hu_inv2 hu_inv1
  refine ⟨fun σ => btil σ + B σ, ⟨V, hV_open, ?_⟩, ?_⟩
  · intro g _ v hv _
    show btil (g * v) + B (g * v) = btil g + B g
    rw [hbtil_loc g v hv (hV_le_H hv), hB_inv g v hv]
  · intro g _ h _
    show c g h = act g • (btil h + B h) - (btil (g * h) + B (g * h)) + (btil g + B g)
    have h2 : c g h = u g h + (act g • btil h - btil (g * h) + btil g) := by
      show c g h = (c g h - (act g • btil h - btil (g * h) + btil g))
        + (act g • btil h - btil (g * h) + btil g)
      abel
    rw [h2, ← hB_eq g h, smul_add]
    abel

end Work.SSGRoute
