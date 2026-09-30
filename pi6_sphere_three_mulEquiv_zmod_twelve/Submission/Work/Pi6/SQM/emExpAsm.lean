import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.Pi6.SQASM.connHomology
import Submission.Work.Pi6.EMODD.sphTwoPi
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! Guidance from the project lead (the requester):

SQM assembly. Read REFS/NOTES_LEAD_SQM.md §5 "emExpAsm" (K₃ part and K₄ part, every step listed). Every input is a
hypothesis. K₄ part: two loop spaces (Path x₀ x₀, then Path (Path.refl x₀) (Path.refl x₀)), σ bijective at n = 3 on
K₄ (b = 4) and n = 2 on K₃ (b = 3), the chain c2, c3, c4, c5 of SigmaStar, (e) twice, then BocksteinSqTwo,
SqOneInjective, EMMod2 part 1 and TorsionOfNonliftable (n = 7). K₃ part is the short version (n = 5).
Delegate the cocycle side conditions (x∪ᵢx cocycle from Cup1Cob/Cup2Cob/Cup3Cob) as one helper.
-/

set_option maxHeartbeats 1600000

namespace Work.Pi6.SQM

open Work.Cohomology (Cochain cochainDiff)

noncomputable section

/-! ## Elementary helpers: `𝔽₂`-cochains of characteristic two, evaluation of `0`, casts -/

open scoped Simplicial

theorem emExp_zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc z + z = (2:ℕ) • z := (two_nsmul z).symm
    _ = (2 : ZMod 2) * z := nsmul_eq_mul 2 z
    _ = 0 := by rw [h2, zero_mul]

theorem emExp_cochain_add_self {X : SSet} {k : ℕ} (a : Cochain F2 X k) : a + a = 0 := by
  apply LinearMap.ext
  intro z
  show a z + a z = 0
  exact emExp_zmod2_add_self (a z)

theorem emExp_genEval_zero {X : SSet} {k : ℕ} (σ : X _⦋k⦌) :
    Work.Cohomology.genEval F2 X (0 : Cochain F2 X k) σ = 0 := by
  simp [Work.Cohomology.genEval]

/-- Transporting a cochain along a self-equality is the identity. -/
theorem emExp_eqRec_self_cast {X : SSet} {p : ℕ} (h : p = p) (y : Cochain F2 X p) :
    (h ▸ y) = y := by cases h; rfl

/-! ## The `∪₁`, `∪₂`, `∪₃` squares of a cocycle are cocycles -/

theorem emExp_cup1_zero_left {X : SSet} (n m : ℕ) (v : Cochain F2 X m) :
    Work.Cohomology.cup1 F2 X n m 0 v = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_cup1]
  simp [emExp_genEval_zero]

theorem emExp_cup1_zero_right {X : SSet} (n m : ℕ) (u : Cochain F2 X n) :
    Work.Cohomology.cup1 F2 X n m u 0 = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_cup1]
  simp [emExp_genEval_zero]

theorem emExp_cup1m_zero_left {X : SSet} (n m : ℕ) (v : Cochain F2 X m) :
    Work.Pi6.SQ.cup1m X n m 0 v = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Pi6.SQ.genEval_cup1m]
  simp [Work.Cohomology.genEval_cup1, emExp_genEval_zero]

theorem emExp_cup1m_zero_right {X : SSet} (n m : ℕ) (u : Cochain F2 X n) :
    Work.Pi6.SQ.cup1m X n m u 0 = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Pi6.SQ.genEval_cup1m]
  simp [Work.Cohomology.genEval_cup1, emExp_genEval_zero]

theorem emExp_cup2_zero_left {X : SSet} (n m : ℕ) (v : Cochain F2 X m) :
    Work.Pi6.SQ.cup2 X n m 0 v = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Pi6.SQ.genEval_cup2]
  simp [emExp_genEval_zero]

theorem emExp_cup2_zero_right {X : SSet} (n m : ℕ) (u : Cochain F2 X n) :
    Work.Pi6.SQ.cup2 X n m u 0 = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Pi6.SQ.genEval_cup2]
  simp [emExp_genEval_zero]

theorem emExp_cup3_zero_left {X : SSet} (n m : ℕ) (v : Cochain F2 X m) :
    Work.Pi6.SQM.cup3 X n m 0 v = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Pi6.SQM.genEval_cup3]
  simp [Work.Pi6.SQM.cup3Val, emExp_genEval_zero]

theorem emExp_cup3_zero_right {X : SSet} (n m : ℕ) (u : Cochain F2 X n) :
    Work.Pi6.SQM.cup3 X n m u 0 = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Pi6.SQM.genEval_cup3]
  simp [Work.Pi6.SQM.cup3Val, emExp_genEval_zero]

/-- The coboundary formula `h1` (`Cup1Cob`) with `u = v = x`, `δx = 0`, gives that `x ∪₁ x` is a
cocycle. -/
theorem emExp_cup1m_cocycle (h1 : Work.Pi6.SQM.Cup1Cob) (X : SSet) (n : ℕ) (x : Cochain F2 X n)
    (hn : 2 ≤ n) (hx : cochainDiff F2 X x = 0) :
    cochainDiff F2 X (Work.Pi6.SQ.cup1m X n n x x) = 0 := by
  have hc : (n+n-1)+1 = n+n := by omega
  have c3 : (n+1)+n-1 = n+n := by omega
  have c4 : n+(n+1)-1 = n+n := by omega
  have h := h1 X n n x x (by omega) (by omega)
  rw [hx] at h
  have hz3 : (c3 ▸ Work.Pi6.SQ.cup1m X (n+1) n (0 : Cochain F2 X (n+1)) x) = 0 := by
    first
      | rw [emExp_cup1m_zero_left]; exact Work.Cohomology.eqRec_zero (R := F2) (X := X) c3
      | rw [emExp_cup1m_zero_left]
  have hz4 : (c4 ▸ Work.Pi6.SQ.cup1m X n (n+1) x (0 : Cochain F2 X (n+1))) = 0 := by
    first
      | rw [emExp_cup1m_zero_right]; exact Work.Cohomology.eqRec_zero (R := F2) (X := X) c4
      | rw [emExp_cup1m_zero_right]
  have hb : ((Nat.add_comm n n) ▸ Work.Cohomology.cup F2 X x x) = Work.Cohomology.cup F2 X x x :=
    emExp_eqRec_self_cast (Nat.add_comm n n) (Work.Cohomology.cup F2 X x x)
  have hRHS : (Work.Cohomology.cup F2 X x x + (Nat.add_comm n n) ▸ Work.Cohomology.cup F2 X x x +
      c3 ▸ Work.Pi6.SQ.cup1m X (n+1) n (0 : Cochain F2 X (n+1)) x +
      c4 ▸ Work.Pi6.SQ.cup1m X n (n+1) x (0 : Cochain F2 X (n+1))) = 0 := by
    rw [hb, hz3, hz4]
    simp [emExp_cochain_add_self]
  have hkey : hc ▸ cochainDiff F2 X (Work.Pi6.SQ.cup1m X n n x x) = 0 := h.trans hRHS
  exact (Work.Cohomology.eqRec_zero (R := F2) (X := X) hc.symm) ▸
    (Work.Cohomology.eqRec_symm_eqRec_self (R := F2) (X := X) hc
      (cochainDiff F2 X (Work.Pi6.SQ.cup1m X n n x x))) ▸
      (congrArg (fun z => hc.symm ▸ z) hkey)

/-- The coboundary formula `h2` (`Cup2Cob`) with `u = v = x`, `δx = 0`, gives that `x ∪₂ x` is a
cocycle. -/
theorem emExp_cup2_cocycle (h2 : Work.Pi6.SQM.Cup2Cob) (X : SSet) (n : ℕ) (x : Cochain F2 X n)
    (hn : 2 ≤ n) (hx : cochainDiff F2 X x = 0) :
    cochainDiff F2 X (Work.Pi6.SQ.cup2 X n n x x) = 0 := by
  have hc : (n+n-2)+1 = n+n-1 := by omega
  have cb : n+n-1 = n+n-1 := by omega
  have c3 : (n+1)+n-2 = n+n-1 := by omega
  have c4 : n+(n+1)-2 = n+n-1 := by omega
  have h := h2 X n n x x (by omega) (by omega)
  rw [hx] at h
  have hz3 : (c3 ▸ Work.Pi6.SQ.cup2 X (n+1) n (0 : Cochain F2 X (n+1)) x) = 0 := by
    first
      | rw [emExp_cup2_zero_left]; exact Work.Cohomology.eqRec_zero (R := F2) (X := X) c3
      | rw [emExp_cup2_zero_left]
  have hz4 : (c4 ▸ Work.Pi6.SQ.cup2 X n (n+1) x (0 : Cochain F2 X (n+1))) = 0 := by
    first
      | rw [emExp_cup2_zero_right]; exact Work.Cohomology.eqRec_zero (R := F2) (X := X) c4
      | rw [emExp_cup2_zero_right]
  have hb : (cb ▸ Work.Pi6.SQ.cup1m X n n x x) = Work.Pi6.SQ.cup1m X n n x x :=
    emExp_eqRec_self_cast cb (Work.Pi6.SQ.cup1m X n n x x)
  have hRHS : (Work.Pi6.SQ.cup1m X n n x x + cb ▸ Work.Pi6.SQ.cup1m X n n x x +
      c3 ▸ Work.Pi6.SQ.cup2 X (n+1) n (0 : Cochain F2 X (n+1)) x +
      c4 ▸ Work.Pi6.SQ.cup2 X n (n+1) x (0 : Cochain F2 X (n+1))) = 0 := by
    rw [hb, hz3, hz4]
    simp [emExp_cochain_add_self]
  have hkey : hc ▸ cochainDiff F2 X (Work.Pi6.SQ.cup2 X n n x x) = 0 := h.trans hRHS
  exact (Work.Cohomology.eqRec_zero (R := F2) (X := X) hc.symm) ▸
    (Work.Cohomology.eqRec_symm_eqRec_self (R := F2) (X := X) hc
      (cochainDiff F2 X (Work.Pi6.SQ.cup2 X n n x x))) ▸
      (congrArg (fun z => hc.symm ▸ z) hkey)

/-- The coboundary formula `h3` (`Cup3Cob`) with `u = v = x`, `δx = 0`, gives that `x ∪₃ x` is a
cocycle. -/
theorem emExp_cup3_cocycle (h3 : Work.Pi6.SQM.Cup3Cob) (X : SSet) (n : ℕ) (x : Cochain F2 X n)
    (hn : 2 ≤ n) (hx : cochainDiff F2 X x = 0) :
    cochainDiff F2 X (Work.Pi6.SQM.cup3 X n n x x) = 0 := by
  have hc : (n+n-3)+1 = n+n-2 := by omega
  have cb : n+n-2 = n+n-2 := by omega
  have c3 : (n+1)+n-3 = n+n-2 := by omega
  have c4 : n+(n+1)-3 = n+n-2 := by omega
  have h := h3 X n n x x (by omega) (by omega)
  rw [hx] at h
  have hz3 : (c3 ▸ Work.Pi6.SQM.cup3 X (n+1) n (0 : Cochain F2 X (n+1)) x) = 0 := by
    first
      | rw [emExp_cup3_zero_left]; exact Work.Cohomology.eqRec_zero (R := F2) (X := X) c3
      | rw [emExp_cup3_zero_left]
  have hz4 : (c4 ▸ Work.Pi6.SQM.cup3 X n (n+1) x (0 : Cochain F2 X (n+1))) = 0 := by
    first
      | rw [emExp_cup3_zero_right]; exact Work.Cohomology.eqRec_zero (R := F2) (X := X) c4
      | rw [emExp_cup3_zero_right]
  have hb : (cb ▸ Work.Pi6.SQ.cup2 X n n x x) = Work.Pi6.SQ.cup2 X n n x x :=
    emExp_eqRec_self_cast cb (Work.Pi6.SQ.cup2 X n n x x)
  have hRHS : (Work.Pi6.SQ.cup2 X n n x x + cb ▸ Work.Pi6.SQ.cup2 X n n x x +
      c3 ▸ Work.Pi6.SQM.cup3 X (n+1) n (0 : Cochain F2 X (n+1)) x +
      c4 ▸ Work.Pi6.SQM.cup3 X n (n+1) x (0 : Cochain F2 X (n+1))) = 0 := by
    rw [hb, hz3, hz4]
    simp [emExp_cochain_add_self]
  have hkey : hc ▸ cochainDiff F2 X (Work.Pi6.SQM.cup3 X n n x x) = 0 := h.trans hRHS
  exact (Work.Cohomology.eqRec_zero (R := F2) (X := X) hc.symm) ▸
    (Work.Cohomology.eqRec_symm_eqRec_self (R := F2) (X := X) hc
      (cochainDiff F2 X (Work.Pi6.SQM.cup3 X n n x x))) ▸
      (congrArg (fun z => hc.symm ▸ z) hkey)


/-! ## Two auxiliary lemmas (helpers for the assembly below) -/

/-- For a cocycle `x` of degree `n ≥ 2` on any simplicial set, the squares `x ∪ᵢ x` (`i = 1, 2, 3`,
Steenrod's convention) and the cup product `x ∪ x` are again cocycles.  This is the "cocycle side
condition" of the assembly: it is immediate from the three coboundary formulas `h1`, `h2`, `h3`
(the two cross terms cancel modulo 2, and `δx = 0` kills the rest) together with the Leibniz rule
for `cup`. -/
theorem sqCocycleAux (h1 : Work.Pi6.SQM.Cup1Cob) (h2 : Work.Pi6.SQM.Cup2Cob)
    (h3 : Work.Pi6.SQM.Cup3Cob) :
    ∀ (X : SSet) (n : ℕ) (x : Cochain F2 X n), 2 ≤ n → cochainDiff F2 X x = 0 →
      cochainDiff F2 X (Work.Pi6.SQ.cup1m X n n x x) = 0 ∧
      cochainDiff F2 X (Work.Pi6.SQ.cup2 X n n x x) = 0 ∧
      cochainDiff F2 X (Work.Pi6.SQM.cup3 X n n x x) = 0 ∧
      cochainDiff F2 X (Work.Cohomology.cup F2 X x x) = 0 := by
  intro X n x hn hx
  exact ⟨emExp_cup1m_cocycle h1 X n x hn hx, emExp_cup2_cocycle h2 X n x hn hx,
    emExp_cup3_cocycle h3 X n x hn hx,
    Work.Cohomology.cochainDiff_cup_of_cocycles (R := F2) (X := X) x x hx hx⟩

/-- The two integral homology hypotheses of `Work.Pi6.SQM.SqOneInjective` hold for every range
model of `K(ℤ/2,2)` through degree `M ≥ 2`: `H₁(X;ℤ) = 0` and `2 · H₂(X;ℤ) = 0`
(`H₁ = 0` from connectivity, `H₂ ≅ ℤ/2` from Hurewicz). -/
theorem kZmod2HurewiczAux (X : Type) [TopologicalSpace X] (x₀ : X) (M : ℕ) (hM : 2 ≤ M)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) M X x₀) :
    Subsingleton (Work.Pi6.HR ℤ X 1) ∧ ∀ a : Work.Pi6.HR ℤ X 2, (2 : ℤ) • a = 0 := by
  have hconn : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) X x₀) :=
    fun i hi => hX.2 i (by omega) (Or.inl hi)
  refine ⟨?_, ?_⟩
  · exact ModuleCat.subsingleton_of_isZero
      (Work.Pi6.SQASM.connHomology x₀ 1 1 (fun j hj => hconn j (by omega)) (by norm_num) le_rfl)
  · intro a
    obtain ⟨eH⟩ := Work.Pi6.EMODD.hurewiczMulEquivSpheres x₀ 1 le_rfl hconn
    obtain ⟨eπ⟩ := hX.1
    have e : Multiplicative (Work.Pi6.HR ℤ X 2) ≃* Multiplicative (ZMod 2) := eH.symm.trans eπ
    have hsq : ∀ z : ZMod 2, Multiplicative.ofAdd z * Multiplicative.ofAdd z = 1 := by
      intro z
      change Multiplicative.ofAdd (z + z) = Multiplicative.ofAdd (0 : ZMod 2)
      congr 1
      calc z + z = (2:ℕ) • z := (two_nsmul z).symm
        _ = (2 : ZMod 2) * z := nsmul_eq_mul 2 z
        _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
    have key : Multiplicative.ofAdd a * Multiplicative.ofAdd a = 1 := by
      apply e.injective
      have h := hsq (Multiplicative.toAdd (e (Multiplicative.ofAdd a)))
      simpa [map_mul] using h
    have hadd : a + a = 0 := by
      have h1 : Multiplicative.ofAdd (a + a) = 1 := key
      have h2 : Multiplicative.ofAdd (a + a) = Multiplicative.ofAdd (0 : Work.Pi6.HR ℤ X 2) := by
        simpa using h1
      exact Multiplicative.ofAdd.injective h2
    rw [two_zsmul, hadd]

/-! ## The assembly -/

theorem emExpAsm (hS : Work.Pi6.SQM.SigmaStar) (hI : Work.Pi6.SQM.SqOneInjective)
    (hB : Work.Pi6.SQM.BocksteinSqTwo) (hT : Work.Pi6.SQM.TorsionOfNonliftable)
    (h1 : Work.Pi6.SQM.Cup1Cob) (h2 : Work.Pi6.SQM.Cup2Cob) (h3 : Work.Pi6.SQM.Cup3Cob)
    (hM2 : Work.Pi6.EMMod2)
    (hNZ : ∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 3 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀ →
      Nontrivial (Work.Pi6.Coh (ZMod 2) X 2)) :
    Work.Pi6.EMExp := by
  obtain ⟨σ, _hnat, _hc1, hc2, hc3, hc4, hc5, hrange, hlift⟩ := hS
  have sqc := sqCocycleAux h1 h2 h3
  have hnz : ∀ (Y : Type) [TopologicalSpace Y] (y₀ : Y) (M : ℕ), 3 ≤ M →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) M Y y₀ →
      ∃ c : Work.Pi6.Coh (ZMod 2) Y 2, c ≠ 0 := by
    intro Y _ y₀ M hM hY
    obtain ⟨a, b, hab⟩ := hNZ Y y₀ M hM hY
    rcases eq_or_ne a 0 with ha | ha
    · exact ⟨b, fun hb => hab (by rw [ha, hb])⟩
    · exact ⟨a, ha⟩
  refine ⟨?_, ?_⟩
  · -- ## the `K(ℤ/2,3)` part: `H₅(X;ℤ)` contains an element of order `≤ 2` not divisible by `2`
    intro X _ x₀ N hN hX
    -- the loop space
    have hloop : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) (N - 1) (Path x₀ x₀)
        (Path.refl x₀) :=
      Work.Stems.isEMSpaceUpTo_loop' (A := ZMod 2) (m := 3) (by norm_num) x₀ hX
    have h3N : 3 ≤ N - 1 := by omega
    -- a nonzero `ι₂ ∈ H²(ΩX;𝔽₂)` and a representing cocycle `r`
    obtain ⟨c₂, hc₂⟩ := hnz (Path x₀ x₀) (Path.refl x₀) (N - 1) h3N hloop
    obtain ⟨r, hr, hrc⟩ := Work.Cohomology.exists_cohomologyClassOf F2 (SX (Path x₀ x₀)) 2 c₂
    -- `ι₃ = σ⁻¹ι₂ ∈ H³(X;𝔽₂)`
    have hconnX : ∀ i : ℕ, i < 3 → Subsingleton (HomotopyGroup (Fin i) X x₀) :=
      fun i hi => hX.2 i (by omega) (Or.inl hi)
    have hbij := (hrange X x₀ 3 (by norm_num) hconnX 2 (by norm_num)).1 (by norm_num)
    obtain ⟨ix₃, hix₃⟩ := hbij.2 c₂
    obtain ⟨x, hx, hxc⟩ := Work.Cohomology.exists_cohomologyClassOf F2 (SX X) 3 ix₃
    have hσx : σ X x₀ 2 (cls x hx) = cls r hr := by
      calc σ X x₀ 2 (cls x hx) = σ X x₀ 2 ix₃ := congrArg (σ X x₀ 2) hxc
        _ = c₂ := hix₃
        _ = cls r hr := hrc.symm
    have hxnz : cls x hx ≠ 0 := fun h0 => hc₂ (by
      calc c₂ = cls r hr := hrc.symm
        _ = σ X x₀ 2 (cls x hx) := hσx.symm
        _ = σ X x₀ 2 (0 : Work.Pi6.Coh F2 X 3) := congrArg (σ X x₀ 2) h0
        _ = 0 := map_zero (σ X x₀ 2))
    -- cocycle side conditions
    obtain ⟨hxx1, _hxx2, _hxx3, hxxcup⟩ := sqc (SX X) 3 x (by norm_num) hx
    -- `[x∪x] ≠ 0`, hence `[x∪₁x]` is not `ℤ/4`-liftable
    have hsq3 := (hM2.2.1 X x₀ N hN hX).2.2
    have hcupeq : Work.Pi6.cup (ZMod 2) X 3 3 (cls x hx) (cls x hx) =
        cls (Work.Cohomology.cup F2 (SX X) x x) hxxcup :=
      Work.Cohomology.cupH'_apply F2 (SX X) x x hx hx hxxcup
    have hcupnz : cls (Work.Cohomology.cup F2 (SX X) x x) hxxcup ≠ 0 := by
      intro h0
      exact hsq3 (cls x hx) hxnz (by
        calc Work.Pi6.cup (ZMod 2) X 3 3 (cls x hx) (cls x hx)
            = cls (Work.Cohomology.cup F2 (SX X) x x) hxxcup := hcupeq
          _ = 0 := h0)
    have hnl : ¬ Liftable4 (cls (Work.Pi6.SQ.cup1m (SX X) 3 3 x x) hxx1) :=
      fun hl => hcupnz (hB X x hx hxx1 hxxcup hl)
    exact hT X 5 (Work.Pi6.SQ.cup1m (SX X) 3 3 x x) hxx1 hnl
  · -- ## the `K(ℤ/2,4)` part: `H₇(X;ℤ)` contains an element of order `≤ 2` not divisible by `2`
    intro X _ x₀ N hN hX
    -- the two loop spaces
    have hloop3 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) (N - 1) (Path x₀ x₀)
        (Path.refl x₀) :=
      Work.Stems.isEMSpaceUpTo_loop' (A := ZMod 2) (m := 4) (by norm_num) x₀ hX
    have hloop2 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) ((N - 1) - 1)
        (Path (Path.refl x₀) (Path.refl x₀)) (Path.refl (Path.refl x₀)) :=
      Work.Stems.isEMSpaceUpTo_loop' (A := ZMod 2) (m := 3) (by norm_num) (Path.refl x₀) hloop3
    have h10 : 3 ≤ (N - 1) - 1 := by omega
    -- a nonzero `ι₂ ∈ H²(Ω²X;𝔽₂)` and a representing cocycle `r`
    obtain ⟨c₂, hc₂⟩ :=
      hnz (Path (Path.refl x₀) (Path.refl x₀)) (Path.refl (Path.refl x₀)) ((N - 1) - 1) h10 hloop2
    obtain ⟨r, hr, hrc⟩ :=
      Work.Cohomology.exists_cohomologyClassOf F2 (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 c₂
    -- `ι₃ = σ⁻¹ι₂ ∈ H³(ΩX;𝔽₂)`
    have hconn3 : ∀ i : ℕ, i < 3 →
        Subsingleton (HomotopyGroup (Fin i) (Path x₀ x₀) (Path.refl x₀)) :=
      fun i hi => hloop3.2 i (by omega) (Or.inl hi)
    have hbij3 := (hrange (Path x₀ x₀) (Path.refl x₀) 3 (by norm_num) hconn3 2 (by norm_num)).1 (by norm_num)
    obtain ⟨ix₃, hix₃⟩ := hbij3.2 c₂
    obtain ⟨x₃, hx₃, hx₃c⟩ := Work.Cohomology.exists_cohomologyClassOf F2 (SX (Path x₀ x₀)) 3 ix₃
    have hσx₃ : σ (Path x₀ x₀) (Path.refl x₀) 2 (cls x₃ hx₃) = cls r hr := by
      calc σ (Path x₀ x₀) (Path.refl x₀) 2 (cls x₃ hx₃)
          = σ (Path x₀ x₀) (Path.refl x₀) 2 ix₃ := congrArg (σ (Path x₀ x₀) (Path.refl x₀) 2) hx₃c
        _ = c₂ := hix₃
        _ = cls r hr := hrc.symm
    -- `ι₄ = σ⁻¹ι₃ ∈ H⁴(X;𝔽₂)`
    have hconn4 : ∀ i : ℕ, i < 4 → Subsingleton (HomotopyGroup (Fin i) X x₀) :=
      fun i hi => hX.2 i (by omega) (Or.inl hi)
    have hbij4 := (hrange X x₀ 4 (by norm_num) hconn4 3 (by norm_num)).1 (by norm_num)
    obtain ⟨ix₄, hix₄⟩ := hbij4.2 (cls x₃ hx₃)
    obtain ⟨x₄, hx₄, hx₄c⟩ := Work.Cohomology.exists_cohomologyClassOf F2 (SX X) 4 ix₄
    have hσx₄ : σ X x₀ 3 (cls x₄ hx₄) = cls x₃ hx₃ := by
      calc σ X x₀ 3 (cls x₄ hx₄) = σ X x₀ 3 ix₄ := congrArg (σ X x₀ 3) hx₄c
        _ = cls x₃ hx₃ := hix₄
    -- cocycle side conditions for `s = x₄∪₃x₄`, `y = s∪₃s`, `u = x₃∪₂x₃`, `w = r∪₁r`
    have hs : cochainDiff F2 (SX X) (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄) = 0 :=
      (sqc (SX X) 4 x₄ (by norm_num) hx₄).2.2.1
    have hss : cochainDiff F2 (SX X)
        (Work.Pi6.SQM.cup3 (SX X) 5 5 (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄)
          (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄)) = 0 :=
      (sqc (SX X) 5 (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄) (by norm_num) hs).2.2.1
    have hu : cochainDiff F2 (SX (Path x₀ x₀))
        (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃) = 0 :=
      (sqc (SX (Path x₀ x₀)) 3 x₃ (by norm_num) hx₃).2.1
    have hu2 : cochainDiff F2 (SX (Path x₀ x₀))
        (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 4 4 (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃)
          (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃)) = 0 :=
      (sqc (SX (Path x₀ x₀)) 4 (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃) (by norm_num) hu).2.1
    have hw : cochainDiff F2 (SX (Path (Path.refl x₀) (Path.refl x₀)))
        (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) = 0 :=
      (sqc (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 r (by norm_num) hr).1
    have hw2 : cochainDiff F2 (SX (Path (Path.refl x₀) (Path.refl x₀)))
        (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 3 3
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)) = 0 :=
      (sqc (SX (Path (Path.refl x₀) (Path.refl x₀))) 3
        (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) (by norm_num) hw).1
    have hww2 : cochainDiff F2 (SX (Path (Path.refl x₀) (Path.refl x₀)))
        (Work.Cohomology.cup F2 (SX (Path (Path.refl x₀) (Path.refl x₀)))
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)) = 0 :=
      (sqc (SX (Path (Path.refl x₀) (Path.refl x₀))) 3
        (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) (by norm_num) hw).2.2.2
    -- `[w] ≠ 0` (SqOneInjective on `Ω²X`)
    have hH1 : Subsingleton (Work.Pi6.HR ℤ (Path (Path.refl x₀) (Path.refl x₀)) 1) :=
      (kZmod2HurewiczAux (Path (Path.refl x₀) (Path.refl x₀)) (Path.refl (Path.refl x₀))
        ((N - 1) - 1) (by omega) hloop2).1
    have htor : ∀ a : Work.Pi6.HR ℤ (Path (Path.refl x₀) (Path.refl x₀)) 2, (2 : ℤ) • a = 0 :=
      (kZmod2HurewiczAux (Path (Path.refl x₀) (Path.refl x₀)) (Path.refl (Path.refl x₀))
        ((N - 1) - 1) (by omega) hloop2).2
    have hwnz : cls (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) hw ≠ 0 :=
      fun h0 => hc₂ (by
        calc c₂ = cls r hr := hrc.symm
          _ = 0 := hI (Path (Path.refl x₀) (Path.refl x₀)) hH1 htor r hr hw h0)
    -- `[w∪w] ≠ 0` (EMMod2 clause 1 on `Ω²X`)
    have hM2K2 := hM2.1 (Path (Path.refl x₀) (Path.refl x₀)) (Path.refl (Path.refl x₀))
      ((N - 1) - 1) (by omega) hloop2
    have hwwnz' := hM2K2.2.2
      (cls (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) hw) hwnz
    have hcupeqw : Work.Pi6.cup (ZMod 2) (Path (Path.refl x₀) (Path.refl x₀)) 3 3
        (cls (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) hw)
        (cls (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) hw) =
        cls (Work.Cohomology.cup F2 (SX (Path (Path.refl x₀) (Path.refl x₀)))
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)) hww2 :=
      Work.Cohomology.cupH'_apply F2 (SX (Path (Path.refl x₀) (Path.refl x₀)))
        (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)
        (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) hw hw hww2
    have hwwnz : cls (Work.Cohomology.cup F2 (SX (Path (Path.refl x₀) (Path.refl x₀)))
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)) hww2 ≠ 0 := by
      intro h0
      exact hwwnz' (by
        calc Work.Pi6.cup (ZMod 2) (Path (Path.refl x₀) (Path.refl x₀)) 3 3
              (cls (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) hw)
              (cls (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) hw)
            = cls (Work.Cohomology.cup F2 (SX (Path (Path.refl x₀) (Path.refl x₀)))
              (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)
              (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)) hww2 := hcupeqw
          _ = 0 := h0)
    -- (c2)--(c5) of `SigmaStar`
    have hc2' : σ X x₀ 4 (cls (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄) hs) =
        cls (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃) hu :=
      hc2 X x₀ x₄ hx₄ hs x₃ hx₃ hu hσx₄.symm
    have hc3' : σ (Path x₀ x₀) (Path.refl x₀) 3
        (cls (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃) hu) =
        cls (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) hw :=
      hc3 (Path x₀ x₀) (Path.refl x₀) x₃ hx₃ hu r hr hw hσx₃.symm
    have hc4' : σ X x₀ 6 (cls (Work.Pi6.SQM.cup3 (SX X) 5 5
          (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄) (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄)) hss) =
        cls (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 4 4
          (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃)
          (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃)) hu2 :=
      hc4 X x₀ (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄) hs hss
        (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃) hu hu2 hc2'.symm
    have hc5' : σ (Path x₀ x₀) (Path.refl x₀) 5
        (cls (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 4 4
          (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃)
          (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃)) hu2) =
        cls (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 3 3
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)) hw2 :=
      hc5 (Path x₀ x₀) (Path.refl x₀) (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃) hu hu2
        (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) hw hw2 hc3'.symm
    -- `[y]` (`y = Sq²Sq¹ι₄`) is not `ℤ/4`-liftable
    have hnl : ¬ Liftable4 (cls (Work.Pi6.SQM.cup3 (SX X) 5 5
        (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄) (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄)) hss) := by
      intro hl0
      have hl1 := hlift X x₀ 6 (cls (Work.Pi6.SQM.cup3 (SX X) 5 5
        (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄) (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄)) hss) hl0
      have hl1b : Liftable4 (cls (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 4 4
          (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃)
          (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃)) hu2) := hc4' ▸ hl1
      have hl2 := hlift (Path x₀ x₀) (Path.refl x₀) 5
        (cls (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 4 4
          (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃)
          (Work.Pi6.SQ.cup2 (SX (Path x₀ x₀)) 3 3 x₃ x₃)) hu2) hl1b
      have hl2b : Liftable4 (cls (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 3 3
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)
          (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r)) hw2) := hc5' ▸ hl2
      exact hwwnz (hB (Path (Path.refl x₀) (Path.refl x₀))
        (Work.Pi6.SQ.cup1m (SX (Path (Path.refl x₀) (Path.refl x₀))) 2 2 r r) hw hw2 hww2 hl2b)
    exact hT X 7 (Work.Pi6.SQM.cup3 (SX X) 5 5
      (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄) (Work.Pi6.SQM.cup3 (SX X) 4 4 x₄ x₄)) hss hnl

end

end Work.Pi6.SQM
