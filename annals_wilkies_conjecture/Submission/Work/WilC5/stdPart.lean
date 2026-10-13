/-
  WilC5 — the **standard part** of a model of `TR`.

  `LRc = (ring ⊕ rexpL)[[ℝ]]` has a constant symbol for every real number, so every `LRc`-structure
  `M` comes with a canonical map `r ↦ realConst M r` (`RealConst.lean`).  This module proves that in
  every model `M ⊨ TR = Th(ℝ_rexp)` that map is an order-preserving ring embedding of `ℝ` onto the
  "standard" part of `M`, in the sense that every element of finite value differs from a constant by
  an infinitesimal:

      `∀ x ∈ Fin(M), ∃ r : ℝ, x - realConst M r ∈ μ(M)`.

  This is the decomposition `w = z (1 + ε)`, `v(ε) > 0`, used by vdDMM Lemma 4.2; it needs no
  o-minimality or completeness input beyond the fact that `M` is an ordered field (from
  `tr_ring_field`) carrying a copy of `ℝ` whose interpretation satisfies the first-order sentences
  true on `ℝ`.

  The proof is entirely first-order:

  * a closed `LRc`-sentence holds in `M` as soon as it holds in `ℝ` (`transfer_sent`), because
    `TR = LRc.completeTheory ℝ`;
  * applying this to the sentences `c_{r+s} = c_r + c_s`, `c_{-r} = -c_r`, `c_0 + c_0 = c_0`,
    `c_1 = c_1 * c_1`, `c_1 ≠ c_0`, `c_{r⁻¹} · c_r = c_1` and `∃z, z*z = c_s - c_r` (the last one
    through the definable order `leEL` of `leEL_iff_le.lean`) shows that `r ↦ realConst M r` is an
    order-preserving ring embedding;
  * for `x` with `|x| ≤ (N : M) + 1` the set `S = {r : ℝ | realConst M r < x}` is nonempty and
    bounded above, and `r₀ = sSup S` satisfies `|x - realConst M r₀| ≤ ((n : M) + 1)⁻¹` for every
    natural `n`, which is exactly `IsInfinitesimal`.
-/
import Mathlib
import Submission.Work.WilC5.RealConst
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.RealFacts

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The `LRc`-operations of a model of `TR` are the ambient field operations. -/

section Reductions
variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]

/-- The ring symbols of `LRc` are interpreted by the ambient ring operations. -/
theorem lrcRingReduct_eq_ring (n : ℕ) (f : Language.ring.Functions n) (xs : Fin n → M) :
    @Structure.funMap LRc M _ n (Sum.inl (Sum.inl f)) xs =
      @Structure.funMap Language.ring M _ n f xs :=
  (Work.WilC2.instRingToLRcIsExpansionOn M).map_onFunction f xs

theorem addEL_eq_add (a b : M) : addEL a b = a + b := by
  rw [addEL, ringSymL, lrcRingReduct_eq_ring 2 Ring.addFunc ![a, b] ]
  simp [Ring.CompatibleRing.funMap_add]

theorem mulEL_eq_mul (a b : M) : mulEL a b = a * b := by
  rw [mulEL, ringSymL, lrcRingReduct_eq_ring 2 Ring.mulFunc ![a, b] ]
  simp [Ring.CompatibleRing.funMap_mul]

theorem negEL_eq_neg (a : M) : negEL a = -a := by
  rw [negEL, ringSymL, lrcRingReduct_eq_ring 1 Ring.negFunc ![a] ]
  simp [Ring.CompatibleRing.funMap_neg, Matrix.cons_val_fin_one]

end Reductions

/-! ## 2. The same reductions on `ℝ`.

`ℝ` carries its structure as an `LEc`-structure (`Bridge.lean`), and the standard `LRc`-structure is
the `rexp`-reduct of it (`reductStruct_real_eq`), so the `LRc`-operations on `ℝ` reduce to the `LEc`
operations whose values are computed in `RealFacts.lean`. -/

section ReductionsReal

theorem lrc_to_LEc (n : ℕ) (g : Language.ring.Functions n) (xs : Fin n → ℝ) :
    @Structure.funMap LRc ℝ (inferInstance) n (Sum.inl (Sum.inl g)) xs =
      @Structure.funMap LEc ℝ _ n (Sum.inl (Sum.inl g)) xs := by
  rw [show (inferInstance : LRc.Structure ℝ) = Work.WilC5.reductStruct ℝ
        from Work.WilC5.reductStruct_real_eq.symm]
  rfl

theorem addEL_real (a b : ℝ) : addEL a b = a + b := by
  rw [addEL, ringSymL, lrc_to_LEc 2 Ring.addFunc ![a, b] ]
  exact Work.WilC5.addE_real a b

theorem mulEL_real (a b : ℝ) : mulEL a b = a * b := by
  rw [mulEL, ringSymL, lrc_to_LEc 2 Ring.mulFunc ![a, b] ]
  exact Work.WilC5.mulE_real a b

theorem negEL_real (a : ℝ) : negEL a = -a := by
  rw [negEL, ringSymL, lrc_to_LEc 1 Ring.negFunc ![a] ]
  exact Work.WilC5.negE_real a

end ReductionsReal

/-! ## 3. Constant terms and their realization. -/

section ConstTerms

/-- The `LRc`-term naming the constant `r : ℝ`. -/
def constTermL {α : Type} (r : ℝ) : LRc.Term α :=
  @Term.func LRc α 0 (Sum.inr r) ![]

theorem realConst_funMap (M : Type) [inst : LRc.Structure M] (r : ℝ) :
    @realConst M inst r = @Structure.funMap LRc M inst 0 (Sum.inr r) ![] := rfl

theorem realize_constTermL {M : Type} [LRc.Structure M] {α : Type} (v : α → M) (r : ℝ) :
    Term.realize v (constTermL (α := α) r) = @realConst M _ r := by
  rw [constTermL, @Term.realize_func LRc M _ α v 0 (Sum.inr r) ![] ]
  rw [realConst_funMap]
  congr 1
  exact Work.WilC5.fin0_funext _ _

theorem realConst_of_reduct (r : ℝ) :
    @realConst ℝ (Work.WilC5.reductStruct ℝ) r = r := by
  rw [realConst_funMap]
  rfl

/-- On the standard structure, the constant attached to `r` is `r` itself. -/
theorem realConst_real (r : ℝ) : realConst ℝ r = r := by
  have h : realConst ℝ r = @realConst ℝ (Work.WilC5.reductStruct ℝ) r := by
    rw [Work.WilC5.reductStruct_real_eq]
  rw [h]
  exact realConst_of_reduct r

end ConstTerms

/-! ## 4. Transfer of closed `LRc`-sentences from `ℝ` to a model of `TR`. -/

section Transfer

theorem transfer_sent {M : Type} [LRc.Structure M] (hM : M ⊨ TR)
    (φ : LRc.BoundedFormula Empty 0)
    (hR : φ.Realize (emptyVar : Empty → ℝ) Fin.elim0) :
    φ.Realize (emptyVar : Empty → M) Fin.elim0 :=
  transfer_LRc hM φ (fun xs => by
      rw [Work.WilC5.fin0_funext xs Fin.elim0]
      exact hR) Fin.elim0

end Transfer

/-! ## 5. The identities satisfied by the constants of a model of `TR`. -/

section ConstFacts
variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]

/-- `c_{r+s} = c_r + c_s`. -/
def addSent (r s : ℝ) : LRc.BoundedFormula Empty 0 :=
  Term.bdEqual (constTermL (α := Empty ⊕ Fin 0) (r + s))
    (tAddL (constTermL (α := Empty ⊕ Fin 0) r) (constTermL (α := Empty ⊕ Fin 0) s))

theorem addSent_realize {M : Type} [LRc.Structure M] (r s : ℝ) :
    (addSent r s).Realize (emptyVar : Empty → M) Fin.elim0 ↔
      realConst M (r + s) = addEL (realConst M r) (realConst M s) := by
  rw [addSent, BoundedFormula.realize_bdEqual]
  simp only [realize_constTermL, realize_tAddL]

theorem realConst_add (r s : ℝ) :
    realConst M (r + s) = realConst M r + realConst M s := by
  have h := (addSent_realize (M := M) r s).mp
    (transfer_sent (M := M) inferInstance (addSent r s) (by
      rw [addSent_realize]
      simp only [realConst_real, addEL_real]))
  simpa only [addEL_eq_add] using h

/-- `c_{-r} = -c_r`. -/
def negSent (r : ℝ) : LRc.BoundedFormula Empty 0 :=
  Term.bdEqual (constTermL (α := Empty ⊕ Fin 0) (-r))
    (tNegL (constTermL (α := Empty ⊕ Fin 0) r))

theorem negSent_realize {M : Type} [LRc.Structure M] (r : ℝ) :
    (negSent r).Realize (emptyVar : Empty → M) Fin.elim0 ↔
      realConst M (-r) = negEL (realConst M r) := by
  rw [negSent, BoundedFormula.realize_bdEqual]
  simp only [realize_constTermL, realize_tNegL]

theorem realConst_neg (r : ℝ) : realConst M (-r) = -realConst M r := by
  have h := (negSent_realize (M := M) r).mp
    (transfer_sent (M := M) inferInstance (negSent r) (by
      rw [negSent_realize]
      simp only [realConst_real, negEL_real]))
  simpa only [negEL_eq_neg] using h

/-- `c_0 + c_0 = c_0`. -/
def zeroSent : LRc.BoundedFormula Empty 0 :=
  Term.bdEqual
    (tAddL (constTermL (α := Empty ⊕ Fin 0) 0) (constTermL (α := Empty ⊕ Fin 0) 0))
    (constTermL (α := Empty ⊕ Fin 0) 0)

theorem zeroSent_realize {M : Type} [LRc.Structure M] :
    zeroSent.Realize (emptyVar : Empty → M) Fin.elim0 ↔
      addEL (realConst M 0) (realConst M 0) = realConst M 0 := by
  rw [zeroSent, BoundedFormula.realize_bdEqual]
  simp only [realize_constTermL, realize_tAddL]

theorem realConst_zero : realConst M 0 = 0 := by
  have h := (zeroSent_realize (M := M)).mp
    (transfer_sent (M := M) inferInstance zeroSent (by
      rw [zeroSent_realize]
      simp only [realConst_real, addEL_real]
      ring))
  rw [addEL_eq_add] at h
  linarith

/-- `c_1 = c_1 * c_1`. -/
def squareOneSent : LRc.BoundedFormula Empty 0 :=
  Term.bdEqual (constTermL (α := Empty ⊕ Fin 0) 1)
    (tMulL (constTermL (α := Empty ⊕ Fin 0) 1) (constTermL (α := Empty ⊕ Fin 0) 1))

theorem squareOneSent_realize {M : Type} [LRc.Structure M] :
    squareOneSent.Realize (emptyVar : Empty → M) Fin.elim0 ↔
      realConst M 1 = mulEL (realConst M 1) (realConst M 1) := by
  rw [squareOneSent, BoundedFormula.realize_bdEqual]
  simp only [realize_constTermL, realize_tMulL]

/-- `c_1 ≠ c_0`. -/
def neOneZeroSent : LRc.BoundedFormula Empty 0 :=
  (Term.bdEqual (constTermL (α := Empty ⊕ Fin 0) 1) (constTermL (α := Empty ⊕ Fin 0) 0)).not

theorem neOneZeroSent_realize {M : Type} [LRc.Structure M] :
    neOneZeroSent.Realize (emptyVar : Empty → M) Fin.elim0 ↔
      ¬ (realConst M 1 = realConst M 0) := by
  rw [neOneZeroSent, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual]
  simp only [realize_constTermL]

/-- The interpretation of the constant `1` is the `1` of the field. -/
theorem realConst_one : realConst M 1 = 1 := by
  have h1 := (squareOneSent_realize (M := M)).mp
    (transfer_sent (M := M) inferInstance squareOneSent (by
      rw [squareOneSent_realize]
      simp only [realConst_real, mulEL_real]
      ring))
  have h2 := (neOneZeroSent_realize (M := M)).mp
    (transfer_sent (M := M) inferInstance neOneZeroSent (by
      rw [neOneZeroSent_realize]
      simp only [realConst_real]
      norm_num))
  rw [mulEL_eq_mul] at h1
  rw [realConst_zero] at h2
  have key : realConst M 1 * (realConst M 1 - 1) = 0 := by nlinarith [h1]
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h h2
  · linarith

/-- `c_{r⁻¹} * c_r = c_1`. -/
def invSent (r : ℝ) : LRc.BoundedFormula Empty 0 :=
  Term.bdEqual
    (tMulL (constTermL (α := Empty ⊕ Fin 0) r⁻¹) (constTermL (α := Empty ⊕ Fin 0) r))
    (constTermL (α := Empty ⊕ Fin 0) 1)

theorem invSent_realize {M : Type} [LRc.Structure M] (r : ℝ) :
    (invSent r).Realize (emptyVar : Empty → M) Fin.elim0 ↔
      mulEL (realConst M r⁻¹) (realConst M r) = realConst M 1 := by
  rw [invSent, BoundedFormula.realize_bdEqual]
  simp only [realize_constTermL, realize_tMulL]

theorem realConst_inv (r : ℝ) (hr : r ≠ 0) :
    realConst M r⁻¹ = (realConst M r)⁻¹ := by
  have h := (invSent_realize (M := M) r).mp
    (transfer_sent (M := M) inferInstance (invSent r) (by
      rw [invSent_realize]
      simp only [realConst_real, mulEL_real]
      exact inv_mul_cancel₀ hr))
  rw [mulEL_eq_mul, realConst_one] at h
  exact eq_inv_of_mul_eq_one_left h

/-- `c_r ≤ c_s` (`leEL`, the definable order of the ring reduct). -/
def leSent (r s : ℝ) : LRc.BoundedFormula Empty 0 :=
  leFormL (constTermL (α := Empty ⊕ Fin 0) r) (constTermL (α := Empty ⊕ Fin 0) s)

theorem leSent_realize {M : Type} [LRc.Structure M] (r s : ℝ) :
    (leSent r s).Realize (emptyVar : Empty → M) Fin.elim0 ↔
      leEL (realConst M r) (realConst M s) := by
  rw [leSent, leFormL_realize]
  simp only [realize_constTermL]

/-- The map `r ↦ realConst M r` is monotone. -/
theorem realConst_le (r s : ℝ) (h : r ≤ s) : realConst M r ≤ realConst M s := by
  have hφ := transfer_sent (M := M) inferInstance (leSent r s) (by
    rw [leSent_realize]
    simp only [realConst_real]
    exact (leEL_real r s).mpr h)
  rw [leSent_realize] at hφ
  exact (leEL_iff_le (M := M) inferInstance (realConst M r) (realConst M s)).mp hφ

theorem realConst_natCast (n : ℕ) : realConst M (n : ℝ) = (n : M) := by
  induction n with
  | zero => rw [Nat.cast_zero, realConst_zero, Nat.cast_zero]
  | succ n ih =>
      rw [Nat.cast_succ, realConst_add, ih, realConst_one, Nat.cast_succ]

theorem realConst_natCast_add_one (n : ℕ) :
    realConst M ((n : ℝ) + 1) = (n : M) + 1 := by
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) from by push_cast; ring]
  rw [realConst_natCast]
  push_cast
  ring

end ConstFacts

/-! ## 6. The standard part theorem. -/

/-- **The standard part theorem.**  Every element of finite value in a model of `TR` is
infinitesimally close to a constant. (The statement below is the frozen one.) -/
theorem stdPart {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR] {x : M}
    (hx : Work.WilC5.IsFiniteVal x) :
    ∃ r : ℝ, Work.WilC5.IsInfinitesimal (x - Work.WilC5.realConst M r) := by
  obtain ⟨N, hN⟩ := hx
  have hNlow : -((N : M) + 1) ≤ x := (abs_le.mp hN).1
  have hNhigh : x ≤ (N : M) + 1 := (abs_le.mp hN).2
  -- the cut that `x` makes among the constants
  set S : Set ℝ := {r : ℝ | realConst M r < x} with hSdef
  have hSne : S.Nonempty := by
    refine ⟨-(N + 2 : ℝ), ?_⟩
    simp only [hSdef, Set.mem_ofPred_eq]
    have hneg : realConst M (-(N + 2 : ℝ)) = -((N : M) + 2) := by
      rw [realConst_neg]
      rw [show (N + 2 : ℝ) = ((N + 2 : ℕ) : ℝ) from by push_cast; ring]
      rw [realConst_natCast]
      push_cast
      ring
    rw [hneg]
    linarith
  have hSbdd : BddAbove S := by
    refine ⟨(N : ℝ) + 1, ?_⟩
    intro r hr
    simp only [hSdef, Set.mem_ofPred_eq] at hr
    by_contra hcon
    have hcon' : (N : ℝ) + 1 < r := not_le.mp hcon
    have hle : realConst M ((N : ℝ) + 1) ≤ realConst M r := realConst_le _ _ (le_of_lt hcon')
    rw [realConst_natCast_add_one] at hle
    linarith
  refine ⟨sSup S, ?_⟩
  intro K
  set e : ℝ := ((K : ℝ) + 1)⁻¹ with hedef
  have hepos : 0 < e := by positivity
  have hlt1 : sSup S - e < sSup S := by linarith
  obtain ⟨r₁, hr₁S, hr₁⟩ := (lt_csSup_iff hSbdd hSne).mp hlt1
  have hr₁S' : realConst M r₁ < x := hr₁S
  have hlow : realConst M (sSup S) - realConst M e < x := by
    have hsub : realConst M (sSup S - e) = realConst M (sSup S) - realConst M e := by
      simp only [sub_eq_add_neg, realConst_add, realConst_neg]
    rw [← hsub]
    exact lt_of_le_of_lt (realConst_le _ _ (le_of_lt hr₁)) hr₁S'
  have hup : x ≤ realConst M (sSup S) + realConst M e := by
    have hnot : ¬ (realConst M (sSup S + e) < x) := by
      intro hlt
      have hmem : sSup S + e ∈ S := by simpa only [hSdef, Set.mem_ofPred_eq] using hlt
      have := le_csSup hSbdd hmem
      linarith
    have hxle : x ≤ realConst M (sSup S + e) := not_lt.mp hnot
    rwa [realConst_add] at hxle
  have key : |x - realConst M (sSup S)| ≤ realConst M e :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have heval : realConst M e = ((K : M) + 1)⁻¹ := by
    have hcast : e = (((K + 1 : ℕ)) : ℝ)⁻¹ := by
      rw [hedef]
      congr 1
      exact (Nat.cast_succ K).symm
    rw [hcast, realConst_inv _ (by positivity), realConst_natCast]
    push_cast
    ring
  rwa [heval] at key

end Work.WilC5
