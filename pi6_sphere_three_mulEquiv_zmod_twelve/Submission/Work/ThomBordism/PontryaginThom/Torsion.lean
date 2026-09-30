import Submission.Work.ThomBordism.PontryaginThom.Rational

/-!
# Rationalisation and torsion: the converse, and the rational form of the detection property

`Rational.lean` proves the easy direction: an element with a positive multiple equal to zero dies
after tensoring with `ℚ`.  Here is the converse — for an arbitrary abelian group the kernel of
`M → M ⊗[ℤ] ℚ` is *exactly* the torsion subgroup:

* `torsion_of_tmul_one_eq_zero` — `h ⊗ 1 = 0` implies `N • h = 0` for some `N > 0`;
* `tmul_one_eq_zero_iff` — the two directions together.

The proof goes through the localisation: `M ⊗[ℤ] ℚ ≅ LocalizedModule (nonZeroDivisors ℤ) M`
(`LocalizedModule.equivTensorProduct`), and the kernel of the localisation map is computed by
`IsLocalizedModule.eq_zero_iff`; the localisation of a module at the nonzero integers is where
`IsLocalization.tensorProduct_isLocalizedModule` provides the instance.

## Consequence for this chapter's interface

`ThomTarget.detects_torsion` is the *integral* form of the Grassmann chapter's
`H^{k+8}(T;ℚ) = ℚ{p₁²U, p₂U}` (chosen because the workspace has no coefficient-change functor in
homology).  With the converse above, that integral form follows from its *rational* form, which is
what a rational-cohomology computation actually produces:

* `ThomTarget.detects_rationally` — a class whose two pairings vanish is zero in `H_{k+8}(T;ℤ) ⊗ ℚ`;
* `ThomTarget.detects_torsion_of_rationally` — the integral property from the rational one.

So the only thing to be supplied by the Grassmann chapter on top of its rational statement about
`H^{k+8}(T;ℚ)` is the compatibility of the Kronecker pairing with tensoring by `ℚ` (the pairings
which appear in `detects_rationally` are the integral ones, so no coefficient bookkeeping about the
*classes* is needed here).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open TensorProduct

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

/-! ## The torsion subgroup is the kernel of rationalisation -/

/-- **Torsion is exactly what dies in rational homology.**  For an abelian group `M` and `h : M`,
`h ⊗ 1 = 0` in `M ⊗[ℤ] ℚ` implies that `h` has finite order.

The proof reduces to the localisation `M ⊗[ℤ] ℚ ≅ LocalizedModule (nonZeroDivisors ℤ) M`: the
element corresponds to the fraction `h / 1`, which is zero there exactly when a nonzero integer
kills `h` (`IsLocalizedModule.eq_zero_iff`). -/
theorem torsion_of_tmul_one_eq_zero {M : Type*} [AddCommGroup M] (h : M)
    (hzero : (h ⊗ₜ[ℤ] (1 : ℚ)) = 0) : ∃ N : ℕ, 0 < N ∧ (N : ℤ) • h = 0 := by
  have hone : (1 : ℚ) ⊗ₜ[ℤ] h = 0 := by
    rw [← TensorProduct.comm_tmul ℤ M ℚ h (1 : ℚ), hzero, map_zero]
  have hloc := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)
      ((TensorProduct.mk ℤ ℚ M) 1)).mp hone
  obtain ⟨s, hs⟩ := hloc
  have hs' : (s : ℤ) • h = 0 := by simpa only [Submonoid.smul_def] using hs
  have hne : (s : ℤ) ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).mp s.2
  refine ⟨s.val.natAbs, (Int.natAbs_pos).mpr hne, ?_⟩
  rcases lt_trichotomy (s : ℤ) 0 with hneg | hz | hpos
  · have h1 : (s.val.natAbs : ℤ) = -s.val := by
      rw [← Int.natAbs_neg s.val, Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ -s.val)]
    rw [h1, neg_zsmul, hs', neg_zero]
  · exact absurd hz hne
  · have h1 : (s.val.natAbs : ℤ) = s.val := Int.natAbs_of_nonneg hpos.le
    rw [h1]
    exact hs'

/-- **The kernel of rationalisation is the torsion subgroup**, in `iff` form. -/
theorem tmul_one_eq_zero_iff {M : Type*} [AddCommGroup M] (h : M) :
    (h ⊗ₜ[ℤ] (1 : ℚ) = 0) ↔ ∃ N : ℕ, 0 < N ∧ (N : ℤ) • h = 0 :=
  ⟨torsion_of_tmul_one_eq_zero h, fun ⟨N, hN, hh⟩ => tmul_one_eq_zero_of_nsmul_eq_zero h hN hh⟩

/-! ## The rational form of the detection property -/

/-- **The rational form of the detection property** of a universal Thom target: a degree-`(k+8)`
homology class whose Kronecker pairings with `p₁²U` and `p₂U` vanish is already zero after tensoring
with `ℚ`.  (The pairings are the integral ones, so no coefficient bookkeeping on the classes is
needed; this is the form in which a rational-cohomology computation — "`p₁²U` and `p₂U` span the
rational dual" — is consumed.) -/
def ThomTarget.detects_rationally {k : ℕ} (D : ThomTarget k) : Prop :=
  ∀ y : (chainC ℤ (ssetOf D.T)).homology (k + 8),
    D.pair1 y = 0 → D.pair2 y = 0 → y ⊗ₜ[ℤ] (1 : ℚ) = 0

/-- **The integral detection property follows from the rational one**: `detects_rationally` for a
Thom target gives `detects_torsion`, by `torsion_of_tmul_one_eq_zero`. -/
theorem ThomTarget.detects_torsion_of_rationally {k : ℕ} (D : ThomTarget k)
    (h : D.detects_rationally) :
    ∀ y : (chainC ℤ (ssetOf D.T)).homology (k + 8),
      D.pair1 y = 0 → D.pair2 y = 0 → ∃ N : ℕ, 0 < N ∧ (N : ℤ) • y = 0 := by
  intro y h1 h2
  have h' := h y h1 h2
  rw [show (HomologicalComplex.homology (chainC ℤ (ssetOf D.T)) (k + 8)).isModule
      = AddCommGroup.toIntModule ↥((chainC ℤ (ssetOf D.T)).homology (k + 8))
      from Subsingleton.elim _ _] at h'
  exact torsion_of_tmul_one_eq_zero y h'

/-- **A `ℤ`-linear functional extends to the rationalisation.**  For `f : M →ₗ[ℤ] ℤ` there is a
`ℤ`-linear `Φ : M ⊗[ℤ] ℚ →ₗ[ℤ] ℚ` with `Φ (y ⊗ q) = q · f y` — the `ℚ`-bilinear extension of `f`,
which exists because the map `(y, q) ↦ q · f y` is `ℤ`-bilinear. -/
theorem exists_rat_lift {M : Type*} [AddCommGroup M] (f : M →ₗ[ℤ] ℤ) :
    ∃ Φ : TensorProduct ℤ M ℚ →ₗ[ℤ] ℚ,
      ∀ (y : M) (q : ℚ), Φ (TensorProduct.tmul ℤ y q) = q * (f y : ℚ) := by
  refine ⟨TensorProduct.lift (LinearMap.mk₂ ℤ (fun y q => q * (f y : ℚ)) ?_ ?_ ?_ ?_), ?_⟩
  · intro y y' q
    rw [map_add, Int.cast_add]
    ring
  · intro c y q
    simp only [map_smul, zsmul_eq_mul, Int.cast_mul]
    push_cast
    ring
  · intro y q q'
    ring
  · intro c y q
    simp only [zsmul_eq_mul]
    push_cast
    ring
  · intro y q
    exact TensorProduct.lift.tmul y q

/-- **The Kronecker pairing with a fixed cohomology class extends to the rationalisation of
homology**: `⟨a, ·⟩ : H_n(X;ℤ) →ₗ[ℤ] ℤ` gives a `ℤ`-linear functional on `H_n(X;ℤ) ⊗[ℤ] ℚ` with
`Φ (y ⊗ q) = q · ⟨a, y⟩`.

This is the missing ingredient that lets a rational-cohomology statement about the Thom space (as in
the Grassmann chapter) be fed into `ThomTarget.detects_rationally`: with
`detects_rationally_of_ratspan`, a rational spanning statement in terms of such extensions yields the
*rational* detection property of the target, and `torsion_of_tmul_one_eq_zero` yields the integral
one. -/
theorem exists_kronH_rat_lift (X : SSet) (n : ℕ) (a : (cochainC ℤ X).homology n) :
    ∃ Φ : TensorProduct ℤ ((chainC ℤ X).homology n) ℚ →ₗ[ℤ] ℚ,
      ∀ (y : (chainC ℤ X).homology n) (q : ℚ),
        Φ (TensorProduct.tmul ℤ y q) = q * ((kronH ℤ X n a) y : ℚ) := by
  refine ⟨TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun y q => q * ((kronH ℤ X n a) y : ℚ)) ?_ ?_ ?_ ?_), ?_⟩
  · intro y y' q
    rw [map_add, Int.cast_add]
    ring
  · intro c y q
    simp only [map_smul, zsmul_eq_mul, Int.cast_mul]
    push_cast
    ring
  · intro y q q'
    ring
  · intro c y q
    simp only [zsmul_eq_mul]
    push_cast
    ring
  · intro y q
    exact TensorProduct.lift.tmul y q

/-- **The two forms of the detection property are equivalent**: for a `ThomTarget`, "the pairings
detect torsion" (the structure's own `detects_torsion`) and the rational form
`detects_rationally` carry the same information, by `tmul_one_eq_zero_iff`. -/
theorem ThomTarget.detects_torsion_iff_rationally {k : ℕ} (D : ThomTarget k) :
    (∀ y : (chainC ℤ (ssetOf D.T)).homology (k + 8),
      D.pair1 y = 0 → D.pair2 y = 0 → ∃ N : ℕ, 0 < N ∧ (N : ℤ) • y = 0) ↔
    D.detects_rationally := by
  constructor
  · intro h y h1 h2
    obtain ⟨N, hN, hh⟩ := h y h1 h2
    have := tmul_one_eq_zero_of_nsmul_eq_zero y hN hh
    rw [show (HomologicalComplex.homology (chainC ℤ (ssetOf D.T)) (k + 8)).isModule
        = AddCommGroup.toIntModule ↥((chainC ℤ (ssetOf D.T)).homology (k + 8))
        from Subsingleton.elim _ _]
    exact this
  · exact D.detects_torsion_of_rationally

/-- **`detects_rationally` from the rational spanning of the two classes.**  If two `ℤ`-linear
functionals on the rationalised homology (in practice the `ℚ`-linear ones, restricted) extend the two
Kronecker pairings (`Φᵢ (y ⊗ q) = q · ⟨·, y⟩`)
and detect the zero class, then the *integral* pairings detect the zero class rationally: this is the
form in which a rational-cohomology computation ("`p₁²U`, `p₂U` span the rational dual") delivers the
hypothesis of `ThomTarget.ofRationally`.

(The existence of the extensions `Φᵢ` themselves is the statement that the Kronecker pairing, which
is `ℤ`-linear in the homology class, extends to the rationalisation; it is *not* an extra hypothesis
in practice, since any explicit construction of the rational pairing provides the `Φᵢ`.) -/
theorem detects_rationally_of_ratspan {k : ℕ} (D : ThomTarget k)
    (Φ₁ Φ₂ : ((chainC ℤ (ssetOf D.T)).homology (k + 8) ⊗[ℤ] ℚ) →ₗ[ℤ] ℚ)
    (h1 : ∀ (y : (chainC ℤ (ssetOf D.T)).homology (k + 8)) (q : ℚ),
      Φ₁ (y ⊗ₜ[ℤ] q) = q * (D.pair1 y : ℚ))
    (h2 : ∀ (y : (chainC ℤ (ssetOf D.T)).homology (k + 8)) (q : ℚ),
      Φ₂ (y ⊗ₜ[ℤ] q) = q * (D.pair2 y : ℚ))
    (hspan : ∀ z : (chainC ℤ (ssetOf D.T)).homology (k + 8) ⊗[ℤ] ℚ,
      Φ₁ z = 0 → Φ₂ z = 0 → z = 0) :
    D.detects_rationally := by
  intro y hy1 hy2
  have hz1 : Φ₁ (y ⊗ₜ[ℤ] (1 : ℚ)) = 0 := by rw [h1, hy1]; ring
  have hz2 : Φ₂ (y ⊗ₜ[ℤ] (1 : ℚ)) = 0 := by rw [h2, hy2]; ring
  exact hspan _ hz1 hz2

/-- **The rational detection property from the rational spanning statement, in the form a
rational-cohomology computation produces.**

Hypothesis: *every* pair of `ℤ`-linear extensions `Φ₁`, `Φ₂` of the two Kronecker pairings (such
extensions exist, `exists_kronH_rat_lift`) detects the zero class.  Conclusion: the *integral*
pairings detect the zero class rationally.  In practice a caller supplies the extension properties
and the spanning statement for *their* construction of the rational pairing; this lemma shows that
this is exactly `ThomTarget.detects_rationally`, i.e. one half of a `ThomTarget`. -/
theorem detects_rationally_of_ratspan_all {k : ℕ} (D : ThomTarget k)
    (h : ∀ (Φ₁ Φ₂ : ((chainC ℤ (ssetOf D.T)).homology (k + 8) ⊗[ℤ] ℚ) →ₗ[ℤ] ℚ),
      (∀ (y : (chainC ℤ (ssetOf D.T)).homology (k + 8)) (q : ℚ),
        Φ₁ (y ⊗ₜ[ℤ] q) = q * (D.pair1 y : ℚ)) →
      (∀ (y : (chainC ℤ (ssetOf D.T)).homology (k + 8)) (q : ℚ),
        Φ₂ (y ⊗ₜ[ℤ] q) = q * (D.pair2 y : ℚ)) →
      (∀ z : (chainC ℤ (ssetOf D.T)).homology (k + 8) ⊗[ℤ] ℚ,
        Φ₁ z = 0 → Φ₂ z = 0 → z = 0)) :
    D.detects_rationally := by
  obtain ⟨Φ₁, h1⟩ := exists_kronH_rat_lift (ssetOf D.T) (k + 8) D.p1sqU
  obtain ⟨Φ₂, h2⟩ := exists_kronH_rat_lift (ssetOf D.T) (k + 8) D.p2U
  exact detects_rationally_of_ratspan D Φ₁ Φ₂ h1 h2 (h Φ₁ Φ₂ h1 h2)

/-- **A universal Thom target from the rational statements**: the space, the base point, the two
classes and the connectivity, together with the *rational* detection property, give a `ThomTarget k`
— the integral torsion-detection property is *proved*, not assumed. -/
def ThomTarget.ofRationally (k : ℕ) (T : Type) [TopologicalSpace T] (t₀ : T)
    (p1sqU p2U : (cochainC ℤ (ssetOf T)).homology (k + 8))
    (connected : ∀ i < k, Subsingleton (HomotopyGroup (Fin i) T t₀))
    (hdetect : ∀ y : (chainC ℤ (ssetOf T)).homology (k + 8),
      kronH ℤ (ssetOf T) (k + 8) p1sqU y = 0 →
      kronH ℤ (ssetOf T) (k + 8) p2U y = 0 → y ⊗ₜ[ℤ] (1 : ℚ) = 0) :
    ThomTarget k where
  T := T
  t₀ := t₀
  p1sqU := p1sqU
  p2U := p2U
  connected := connected
  detects_torsion := by
    intro y h1 h2
    have h' := hdetect y h1 h2
    rw [show (HomologicalComplex.homology (chainC ℤ (ssetOf T)) (k + 8)).isModule
        = AddCommGroup.toIntModule ↥((chainC ℤ (ssetOf T)).homology (k + 8))
        from Subsingleton.elim _ _] at h'
    exact torsion_of_tmul_one_eq_zero y h'

end

end Work.ThomBordism.PontryaginThom
