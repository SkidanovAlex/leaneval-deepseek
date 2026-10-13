/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.Ideal.Hilbert.hilbert_sum_lower_bound` (piece 0).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Work.WilE2.BzPort.P45

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.hilbert_sum_lower_bound ====
section

namespace Commons.RingTheory.Ideal.Hilbert
open MvPolynomial

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

attribute [local instance] MvPolynomial.gradedAlgebra

lemma hilbertFun_zero {k : Type*} [Field k] {m : ℕ} (q : Ideal (MvPolynomial (Fin m) k))
    (hq : q ≠ ⊤) :
    hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k 0) = 1 := by
  haveI hfin : Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k 0) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin m) k 0)
  rw [hilbertFun_eq_sub]
  have hfinrank : Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k 0) = 1 := by
    rw [Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule_eq_choose]
    simp
  have hinter : (MvPolynomial.homogeneousSubmodule (Fin m) k 0 ⊓ q.restrictScalars k) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxV, hxq⟩ := hx
    have h1 : MvPolynomial.homogeneousComponent 0 x = x :=
      MvPolynomial.homogeneousComponent_eq_self
        ((MvPolynomial.mem_homogeneousSubmodule 0 x).mp hxV)
    have h2 : MvPolynomial.homogeneousComponent 0 x = MvPolynomial.C ((x).coeff 0) :=
      MvPolynomial.homogeneousComponent_zero x
    have hxC : x = MvPolynomial.C ((x).coeff 0) := h1.symm.trans h2
    have hxq' : MvPolynomial.C ((x).coeff 0) ∈ q := hxC ▸ hxq
    by_contra hc
    have hc0 : (x).coeff 0 ≠ 0 := by
      intro h; exact hc (by rw [hxC, h, MvPolynomial.C_0])
    have h1' : (1 : MvPolynomial (Fin m) k) ∈ q := by
      have hm := q.mul_mem_left (MvPolynomial.C ((x).coeff 0)⁻¹) hxq'
      rwa [← MvPolynomial.C_mul, inv_mul_cancel₀ hc0, MvPolynomial.C_1] at hm
    exact hq ((Ideal.eq_top_iff_one q).mpr h1')
  rw [hfinrank, hinter]
  simp

theorem lower_bound_aux {k : Type*} [Field k] {m : ℕ} (d : ℕ) :
    ∀ (q : Ideal (MvPolynomial (Fin m) k))
      (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q),
      ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = (d : WithBot ℕ∞) →
      ∃ c : ℚ, 0 < c ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
        c * ((t : ℚ) + 1) ^ d ≤ ((∑ u ∈ Finset.range (t + 1), hilbertFun q
          (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℚ) := by
  induction d with
  | zero =>
      intro q hq hd
      have hqne : q ≠ ⊤ := by
        intro hqt
        haveI : Subsingleton (MvPolynomial (Fin m) k ⧸ q) :=
          Ideal.Quotient.subsingleton_iff.mpr hqt
        rw [ringKrullDim_eq_bot_of_subsingleton] at hd
        exact WithBot.bot_ne_coe hd
      refine ⟨1, one_pos, 0, fun t _ => ?_⟩
      have h0 : hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k 0) = 1 :=
        hilbertFun_zero q hqne
      have hmem : (0 : ℕ) ∈ Finset.range (t + 1) := Finset.mem_range.mpr (Nat.succ_pos t)
      have hle : hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k 0)
          ≤ ∑ u ∈ Finset.range (t + 1), hilbertFun q
              (MvPolynomial.homogeneousSubmodule (Fin m) k u) :=
        Finset.single_le_sum (f := fun u => hilbertFun q
            (MvPolynomial.homogeneousSubmodule (Fin m) k u)) (fun _ _ => Nat.zero_le _) hmem
      rw [h0] at hle
      have : (1 : ℚ) ≤ ((∑ u ∈ Finset.range (t + 1), hilbertFun q
          (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℚ) := by exact_mod_cast hle
      simpa using this
  | succ n ih =>
      intro q hq hd
      obtain ⟨p, hpmem, hpd⟩ := Commons.RingTheory.KrullDimension.exists_minimalPrime_ringKrullDim_quotient_eq q (n + 1) hd
      haveI hpIsPrime : p.IsPrime := hpmem.1.1
      have hqle : q ≤ p := hpmem.1.2
      have hphom := minimalPrimes_homogeneousComponent_mem hq hpmem
      have hple := minimalPrimes_le_idealOfVars q hq hpmem
      have hex : ∃ i : Fin m, MvPolynomial.X i ∉ p := by
        by_contra hcon
        push Not at hcon
        have hle : MvPolynomial.idealOfVars (Fin m) k ≤ p := by
          rw [MvPolynomial.idealOfVars]
          refine Ideal.span_le.mpr (fun x hx => ?_)
          rw [Set.mem_range] at hx
          obtain ⟨i, rfl⟩ := hx
          exact hcon i
        have hle0 := ringKrullDim_le_zero_of_minimalPrimes_idealOfVars_le hq hpmem hle
        rw [hd] at hle0
        have hgt : ((0 : ℕ) : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞) := by
          exact_mod_cast Nat.succ_pos n
        exact (not_le_of_gt hgt) hle0
      obtain ⟨i, hi⟩ := hex
      have hf0 : (MvPolynomial.X i : MvPolynomial (Fin m) k) ≠ 0 := MvPolynomial.X_ne_zero (R := k) i
      have hproper : p ⊔ Ideal.span {MvPolynomial.X i} ≠ ⊤ := by
        intro htop
        have hle : p ⊔ Ideal.span {MvPolynomial.X i} ≤ MvPolynomial.idealOfVars (Fin m) k := by
          refine sup_le hple ?_
          rw [Ideal.span_le]
          rintro x hx
          rw [Set.mem_singleton_iff] at hx
          rw [hx, MvPolynomial.idealOfVars]
          exact Ideal.subset_span ⟨i, rfl⟩
        exact idealOfVars_ne_top (top_le_iff.mp (htop ▸ hle))
      obtain ⟨d', hd'p, hd'ne, hd'K⟩ :=
        dim_quotient_sup_span_eq_dim_sub_one p hphom hi hf0 hproper
      have hd'eq : d' = n + 1 := by
        have h1 : ((d' : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) :=
          (WithBot.coe_inj (α := ℕ∞)).mp (hd'p.symm.trans hpd)
        exact WithTop.coe_inj.mp h1
      have hphomI : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) p := by
        rw [Ideal.IsHomogeneous.iff_eq]
        refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ p) ?_
        intro y hy
        rw [← MvPolynomial.sum_homogeneousComponent y]
        refine Ideal.sum_mem _ fun j _ => ?_
        exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
          ⟨j, MvPolynomial.homogeneousComponent_mem j y⟩ (hphom y hy j)
      have hKhom : ∀ x ∈ p ⊔ Ideal.span {MvPolynomial.X i}, ∀ j,
          MvPolynomial.homogeneousComponent j x ∈ p ⊔ Ideal.span {MvPolynomial.X i} := by
        have hsup : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k)
            (p ⊔ Ideal.span {MvPolynomial.X i}) :=
          hphomI.sup (homogeneous_span_singleton (MvPolynomial.isHomogeneous_X k i))
        intro x hx j
        exact (MvPolynomial.mem_iff_homogeneousComponent_mem hsup x).mp hx j
      have hdimK : ringKrullDim (MvPolynomial (Fin m) k ⧸ (p ⊔ Ideal.span {MvPolynomial.X i}))
          = (n : WithBot ℕ∞) := by
        rw [hd'K, hd'eq]
        congr 1
      obtain ⟨c', hc'pos, N', hN'⟩ := ih _ hKhom hdimK
      obtain ⟨c'', hc''pos, N'', hN''⟩ :=
        Commons.Algebra.BigOperators.sum_Icc_pow_lower_bound n N'
      refine ⟨c' * c'', mul_pos hc'pos hc''pos, max (max N' N'') 1, fun t ht => ?_⟩
      haveI hfin : ∀ s : ℕ, Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k s) :=
        fun s => Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin m) k s)
      have htN' : N' ≤ t := le_trans (le_trans (le_max_left N' N'') (le_max_left (max N' N'') 1)) ht
      have htN'' : N'' ≤ t := le_trans (le_trans (le_max_right N' N'') (le_max_left (max N' N'') 1)) ht
      have hbez : ∀ u, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u)
          = ∑ j ∈ Finset.range (u + 1), hilbertFun (p ⊔ Ideal.span {MvPolynomial.X i})
              (MvPolynomial.homogeneousSubmodule (Fin m) k j) :=
        fun u => hilbertFun_eq_sum_hilbertFun_sup_span_X p hphom hi hproper u
      have hs1 : ∑ u ∈ Finset.range (t + 1), hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u)
          ≤ ∑ u ∈ Finset.range (t + 1), hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k u) :=
        Finset.sum_le_sum (fun u _ => hilbertFun_anti hqle _)
      have hsub : Finset.Icc N' t ⊆ Finset.range (t + 1) := by
        intro u hu
        rw [Finset.mem_Icc] at hu
        rw [Finset.mem_range]
        omega
      have hsq_icc : ∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u)
          ≤ ∑ u ∈ Finset.range (t + 1), hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => Nat.zero_le _)
      have hterm : ∀ u ∈ Finset.Icc N' t,
          c' * ((u : ℚ) + 1) ^ n ≤ (hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℚ) := by
        intro u hu
        rw [Finset.mem_Icc] at hu
        have h := hN' u hu.1
        have hcast : (∑ j ∈ Finset.range (u + 1), (hilbertFun (p ⊔ Ideal.span {MvPolynomial.X i})
            (MvPolynomial.homogeneousSubmodule (Fin m) k j) : ℚ))
            = (hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℚ) := by
          rw [← Nat.cast_sum, ← hbez u]
        rw [hcast] at h
        exact h
      have hL4 := hN'' t htN''
      have hmul : c' * (c'' * ((t : ℚ) + 1) ^ (n + 1))
          ≤ c' * ∑ j ∈ Finset.Icc N' t, ((j : ℚ) + 1) ^ n :=
        mul_le_mul_of_nonneg_left hL4 hc'pos.le
      have hsum1 : ∑ u ∈ Finset.Icc N' t, c' * ((u : ℚ) + 1) ^ n
          ≤ ∑ u ∈ Finset.Icc N' t, (hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℚ) :=
        Finset.sum_le_sum hterm
      have hfac : ∑ u ∈ Finset.Icc N' t, c' * ((u : ℚ) + 1) ^ n
          = c' * ∑ u ∈ Finset.Icc N' t, ((u : ℚ) + 1) ^ n := by
        rw [Finset.mul_sum]
      have hcast : ∑ u ∈ Finset.Icc N' t, (hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℚ)
          = ((∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℕ) : ℚ) := by
        rw [Nat.cast_sum]
      have hchain1 : c' * c'' * ((t : ℚ) + 1) ^ (n + 1)
          ≤ ((∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℕ) : ℚ) := by
        calc c' * c'' * ((t : ℚ) + 1) ^ (n + 1)
            = c' * (c'' * ((t : ℚ) + 1) ^ (n + 1)) := by ring
          _ ≤ c' * ∑ j ∈ Finset.Icc N' t, ((j : ℚ) + 1) ^ n := hmul
          _ = ∑ u ∈ Finset.Icc N' t, c' * ((u : ℚ) + 1) ^ n := hfac.symm
          _ ≤ ∑ u ∈ Finset.Icc N' t, (hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℚ) := hsum1
          _ = ((∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℕ) : ℚ) := hcast
      have hnat : (∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u))
          ≤ ∑ u ∈ Finset.range (t + 1), hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k u) :=
        le_trans hsq_icc hs1
      have hcast2 : ((∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℕ) : ℚ)
          ≤ ((∑ u ∈ Finset.range (t + 1), hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℚ) := by
        exact_mod_cast hnat
      exact le_trans hchain1 hcast2

theorem hilbert_sum_lower_bound {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = (d : WithBot ℕ∞)) :
    ∃ c : ℚ, 0 < c ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      c * ((t : ℚ) + 1) ^ d ≤ ((∑ u ∈ Finset.range (t + 1), Module.finrank k
        (Submodule.map (q.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k u))) : ℚ) := by
  simpa only [hilbertFun] using lower_bound_aux d q hq hd

end Commons.RingTheory.Ideal.Hilbert

/-!
# Lower bound for the partial sums of the Hilbert function of a homogeneous quotient

For a homogeneous ideal `q` of `k[X₁,…,Xₘ]` with `ringKrullDim (R ⧸ q) = d`, the partial sums
of the Hilbert function grow at least like `C (t+1)^d`.

We prove this by induction on `d`.  A minimal prime `p` of `q` with `dim (R ⧸ p) = d` gives
the reduction to the domain (prime) case.  In the prime case, choosing `Xᵢ ∉ p` produces an
exact relation `HilbertFun p t = ∑_{j ≤ t} HilbertFun (p + (Xᵢ)) j`, so the induction applied
to `p + (Xᵢ)` (whose dimension is `d - 1`) together with the elementary lower bound
`∑_{j=M}^t (j+1)^{d-1} ≥ c (t+1)^d` gives the result.
-/

end


