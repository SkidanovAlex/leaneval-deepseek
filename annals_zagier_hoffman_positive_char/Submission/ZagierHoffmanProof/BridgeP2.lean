import Submission.ZagierHoffmanProof.ChainP
import Submission.ZagierHoffmanProof.HDatum
import Submission.ZagierHoffmanProof.Step3Splitting
import Submission.ZagierHoffmanProof.Counting

/-!
# The global bridge (4.2) for the Anderson–Thakur datum `(s, H_s)`

The `L`-series of the datum `Q_j = H_{s_j}` (the Anderson–Thakur polynomials) evaluates at `θ` to
the `Γ`-multiple of `ζ_A`:

  `π̃^{w}·𝓛(𝔰; H_{s_1},…,H_{s_r})(θ) = (∏_j Γ_{s_j})·ζ_A(𝔰)`,   `Γ_s = 1` (`s ≤ q`), `= θ^q-θ` (`q < s`),

i.e. Ngo Dac's (4.2) `L(𝔰;Q)(θ) = Γ_𝔰·ζ_A(𝔰)·π̃^{-w}` for `Q_j = H_{s_j}`.  This is the
`ambH`-datum analogue of `ATBridge2.bridge` (which is the `Q = 1` case), and is the transcendental
input of Dac's Theorem 6.2 (the `𝒯'_w` route to Theorem D).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The bridge -/

section Bridge

/-- **★★★ THE BRIDGE (4.2) FOR THE `ambH`-DATUM**: for a list `M` of `(exponent, Γ-twisted
Anderson–Thakur polynomial)` the value of the `L`-series is the `Γ`-multiple of `ζ_A` on the
reversed exponent tuple, times `π̃^{-w}`. -/
theorem bridgeP (M : List (ℕ × PowerSeries (Ambient F)))
    (hne : M ≠ [])
    (hQ : ∀ j : Fin M.length,
      (M.get j).2 = ((ambH F (M.get j).1 : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hpos : ∀ j : Fin M.length, 1 ≤ (M.get j).1)
    (hsup : ∀ j : Fin M.length, (M.get j).1 ≤ 2 * Nat.card F - 2)
    (𝔰 : Fin M.length → ℕ+)
    (h𝔰 : ∀ j : Fin M.length, (𝔰 j : ℕ) = (M.get (Fin.rev j)).1)
    (h𝔰q : ∀ j : Fin M.length, (𝔰 j : ℕ) ≤ 2 * Nat.card F - 2) :
    (ambPiTilde F) ^ (∑ j, (𝔰 j : ℕ))
        * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) M) (ambTheta F)
      = (∏ j : Fin M.length, ambGammaF F ((𝔰 j : ℕ))) * ambInfHom F (ζ_A F 𝔰) := by
  rcases M with _ | ⟨a, rest⟩
  · exact absurd rfl hne
  · have hQmem : ∀ x ∈ (a :: rest),
        x.2 = ((ambH F x.1 : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
      intro x hx
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
      rw [← hj]
      exact hQ j
    have hposmem : ∀ x ∈ (a :: rest), 1 ≤ x.1 := by
      intro x hx
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
      rw [← hj]
      exact hpos j
    have hsupmem : ∀ x ∈ (a :: rest), x.1 ≤ 2 * Nat.card F - 2 := by
      intro x hx
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
      rw [← hj]
      exact hsup j
    have hL : ∀ x ∈ (a :: rest), GIsSmall ambGamma ((ambOmega F) ^ x.1 * x.2) := by
      intro x hx
      rw [hQmem x hx]
      exact gIsSmall_ambOmega_pow_mul_ambH F (hposmem x hx)
    have hLse : ∀ x ∈ (a :: rest), GSuperEntire ambGamma x.2 := by
      intro x hx
      rw [hQmem x hx]
      exact gSuperEntire_ambH F x.1
    let e : Fin ((a :: rest).length) → ℕ+ :=
      fun j => ⟨((a :: rest).get j).1, hposmem _ (List.get_mem _ _)⟩
    have he : ∀ j : Fin ((a :: rest).length), e (Fin.rev j) = 𝔰 j :=
      fun j => Subtype.ext (h𝔰 j).symm
    have hYid : ∀ j : Fin ((a :: rest).length), ∀ d : ℕ,
        evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
          ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2)) (ambTheta F)
        = (evalSeriesGen (ambOmega F) (ambTheta F)) ^ ((a :: rest).get j).1
          * ambGammaF F ((a :: rest).get j).1 * ambInfHom F (P F d (e j)) := by
      intro j d
      rw [hQmem _ (List.get_mem _ _)]
      exact evalSeriesGen_frobTwist_ambOmega_pow_ambH F (e j) d
        (hsupmem _ (List.get_mem _ _))
    have hYdecay : ∀ j : Fin ((a :: rest).length), ∀ d : ℕ,
        Valued.v (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
          ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2)) (ambTheta F))
          ≤ 1 * ambRho F ^ d := by
      intro j d
      rw [hQmem _ (List.get_mem _ _)]
      refine le_trans (v_evalSeriesGen_frobTwist_ambOmega_pow_ambH_le F
        (hposmem _ (List.get_mem _ _)) (hsupmem _ (List.get_mem _ _))) (le_of_eq ?_)
      rw [ambRho, ← WithZero.exp_nsmul, nsmul_eq_mul, one_mul, one_mul]
      congr 1
      ring
    rw [evalSeriesGen_atLrGen_chain F (a :: rest) hne hL hLse
      (ambRho_pos F) (ambRho_lt_one F) hYdecay]
    rw [← tsum_mul_left]
    have hpt : ∀ v : Fin ((a :: rest).length) → ℕ,
        ambPiTilde F ^ (∑ j : Fin ((a :: rest).length), (𝔰 j : ℕ))
            * (if StrictMono v then ∏ j : Fin ((a :: rest).length), evalSeriesGen
                (frobTwist (R := Ambient F) (p := Nat.card F) (v j)
                  ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2))
                (ambTheta F) else 0)
          = (∏ j : Fin ((a :: rest).length), ambGammaF F ((a :: rest).get j).1)
            * (if StrictMono v then ∏ j : Fin ((a :: rest).length),
                ambInfHom F (P F (v j) (e j)) else 0) := by
      intro v
      by_cases hv : StrictMono v
      · rw [if_pos hv, if_pos hv]
        have hprod : (∏ j : Fin ((a :: rest).length), evalSeriesGen
              (frobTwist (R := Ambient F) (p := Nat.card F) (v j)
                ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2))
              (ambTheta F))
            = (evalSeriesGen (ambOmega F) (ambTheta F)) ^ (∑ j : Fin ((a :: rest).length),
                ((a :: rest).get j).1)
              * (∏ j : Fin ((a :: rest).length), ambGammaF F ((a :: rest).get j).1)
              * ∏ j : Fin ((a :: rest).length), ambInfHom F (P F (v j) (e j)) := by
          rw [Finset.prod_congr rfl (fun j _ => hYid j (v j)), Finset.prod_mul_distrib,
            Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        rw [hprod]
        have hw : (∑ j : Fin ((a :: rest).length), (𝔰 j : ℕ))
            = ∑ j : Fin ((a :: rest).length), ((a :: rest).get j).1 := by
          have h1 : (∑ j : Fin ((a :: rest).length), (𝔰 j : ℕ))
              = ∑ j : Fin ((a :: rest).length), ((a :: rest).get (Fin.rev j)).1 :=
            Finset.sum_congr rfl (fun j _ => h𝔰 j)
          rw [h1]
          exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin ((a :: rest).length)))
            (fun j => ((a :: rest).get j).1)
        rw [hw]
        rw [← mul_assoc, ← mul_assoc, ← mul_pow, ambPiTilde_mul_eval, one_pow, one_mul]
      · rw [if_neg hv, if_neg hv, mul_zero, mul_zero]
    rw [tsum_congr hpt]
    rw [tsum_mul_left]
    rw [tsum_mono_eq_anti (K := Ambient F) (n := (a :: rest).length)
      (Y := fun j d => ambInfHom F (P F d (e j)))]
    have hconv : (∑' u : Fin ((a :: rest).length) → ℕ,
        (if StrictAnti u then ∏ j, ambInfHom F (P F (u j) (e (Fin.rev j))) else 0))
        = ∑' u : Fin ((a :: rest).length) → ℕ,
        (if StrictAnti u then ∏ j, ambInfHom F (P F (u j) (𝔰 j)) else 0) := by
      refine tsum_congr fun u => ?_
      by_cases h : StrictAnti u
      · rw [if_pos h, if_pos h]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [he j]
      · rw [if_neg h, if_neg h]
    rw [hconv]
    have hprodΓ : (∏ j : Fin ((a :: rest).length), ambGammaF F ((a :: rest).get j).1)
        = ∏ j : Fin ((a :: rest).length), ambGammaF F ((𝔰 j : ℕ)) := by
      calc (∏ j : Fin ((a :: rest).length), ambGammaF F ((a :: rest).get j).1)
          = ∏ j : Fin ((a :: rest).length), ambGammaF F ((a :: rest).get (Fin.rev j)).1 :=
            (Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin ((a :: rest).length)))
              (fun j => ambGammaF F ((a :: rest).get j).1)).symm
        _ = ∏ j : Fin ((a :: rest).length), ambGammaF F ((𝔰 j : ℕ)) := by
            refine Finset.prod_congr rfl (fun j _ => ?_)
            rw [h𝔰 j]
    rw [hprodΓ]
    congr 1
    exact (ambInfHom_zeta_A_eq_chainP F rest.length 𝔰 h𝔰q).symm

end Bridge

/-! ## §2. The multiplied form -/

section BridgeMul

/-- The bridge, with an extra polynomial factor `a`: this is the form in which Step 3 of Dac §5.3
uses it. -/
theorem bridgeP_mul (M : List (ℕ × PowerSeries (Ambient F)))
    (hne : M ≠ [])
    (hQ : ∀ j : Fin M.length,
      (M.get j).2 = ((ambH F (M.get j).1 : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hpos : ∀ j : Fin M.length, 1 ≤ (M.get j).1)
    (hsup : ∀ j : Fin M.length, (M.get j).1 ≤ 2 * Nat.card F - 2)
    (𝔰 : Fin M.length → ℕ+)
    (h𝔰 : ∀ j : Fin M.length, (𝔰 j : ℕ) = (M.get (Fin.rev j)).1)
    (h𝔰q : ∀ j : Fin M.length, (𝔰 j : ℕ) ≤ 2 * Nat.card F - 2)
    (a : Polynomial (Ambient F)) :
    (ambPiTilde F) ^ (∑ j, (𝔰 j : ℕ))
        * (a.eval (ambTheta F)
          * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) M) (ambTheta F))
      = (∏ j : Fin M.length, ambGammaF F ((𝔰 j : ℕ)))
        * (a.eval (ambTheta F) * ambInfHom F (ζ_A F 𝔰)) := by
  rw [show (ambPiTilde F) ^ (∑ j, (𝔰 j : ℕ))
        * (a.eval (ambTheta F)
          * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) M) (ambTheta F))
      = a.eval (ambTheta F) * ((ambPiTilde F) ^ (∑ j, (𝔰 j : ℕ))
          * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) M) (ambTheta F)) from by ring,
    bridgeP F M hne hQ hpos hsup 𝔰 h𝔰 h𝔰q]
  ring

end BridgeMul

/-! ## §3. The `Fin`-indexed tuple form -/

section TupleForm

/-- The `List (ℕ × PowerSeries (Ambient F))` of the Anderson–Thakur datum attached to a
`Fin`-indexed tuple of positive exponents (in the tuple's own order). -/
@[reducible] noncomputable def tupleListH {n : ℕ} (𝔰 : Fin n → ℕ+) :
    List (ℕ × PowerSeries (Ambient F)) :=
  List.ofFn (fun j : Fin n =>
    ((𝔰 j : ℕ), ((ambH F (𝔰 j) : Polynomial (Ambient F)) : PowerSeries (Ambient F))))

/-- The `Polynomial`-level version (`tmF`/`tmL`'s index type). -/
@[reducible] noncomputable def tupleListHP {n : ℕ} (𝔰 : Fin n → ℕ+) :
    List (ℕ × Polynomial (Ambient F)) :=
  List.ofFn (fun j : Fin n => ((𝔰 j : ℕ), (ambH F (𝔰 j) : Polynomial (Ambient F))))

lemma tupleListH_length {n : ℕ} (𝔰 : Fin n → ℕ+) : (tupleListH F 𝔰).length = n :=
  List.length_ofFn

lemma tmCoe_tupleListHP {n : ℕ} (𝔰 : Fin n → ℕ+) :
    tmCoe (K := Ambient F) (tupleListHP F 𝔰) = tupleListH F 𝔰 := by
  simp only [tupleListHP, tupleListH, tmCoe, List.map_ofFn]
  congr 1

/-- The first component of the entries of the reversed datum list. -/
lemma tupleListH_reverse_get_fst {n : ℕ} (𝔰 : Fin n → ℕ+)
    (j : Fin ((tupleListH F 𝔰).reverse).length) :
    (((tupleListH F 𝔰).reverse).get j).1
      = (𝔰 (Fin.cast (by rw [List.length_reverse, tupleListH_length]) (Fin.rev j)) : ℕ) := by
  have hL : (tupleListH F 𝔰).length = n := tupleListH_length F 𝔰
  have h1 : (j : ℕ) < (tupleListH F 𝔰).reverse.length := j.isLt
  have h2 : ((tupleListH F 𝔰).reverse).length = (tupleListH F 𝔰).length :=
    List.length_reverse
  rw [List.get_reverse' (tupleListH F 𝔰) j (by omega), List.get_ofFn]
  refine congrArg (fun k : Fin n => (𝔰 k : ℕ)) ?_
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_rev, List.length_ofFn]
  omega

/-- The second component of the entries of the reversed datum list. -/
lemma tupleListH_reverse_get_snd {n : ℕ} (𝔰 : Fin n → ℕ+)
    (j : Fin ((tupleListH F 𝔰).reverse).length) :
    (((tupleListH F 𝔰).reverse).get j).2
      = ((ambH F ((((tupleListH F 𝔰).reverse).get j).1) : Polynomial (Ambient F))
          : PowerSeries (Ambient F)) := by
  have hL : (tupleListH F 𝔰).length = n := tupleListH_length F 𝔰
  have h1 : (j : ℕ) < (tupleListH F 𝔰).reverse.length := j.isLt
  have h2 : ((tupleListH F 𝔰).reverse).length = (tupleListH F 𝔰).length :=
    List.length_reverse
  rw [List.get_reverse' (tupleListH F 𝔰) j (by omega), List.get_ofFn]


/-- **★★★ THE BRIDGE (4.2) FOR A `Fin`-INDEXED TUPLE**: with the Anderson–Thakur datum
`Q_j = H_{s_j}` and an extra polynomial factor `a`. -/
theorem bridgeP_tuple_mul {r : ℕ} (𝔰 : Fin r → ℕ+) (hr : 0 < r)
    (hsup : ∀ j : Fin r, (𝔰 j : ℕ) ≤ 2 * Nat.card F - 2) (a : Polynomial (Ambient F)) :
    (ambPiTilde F) ^ (∑ j : Fin r, (𝔰 j : ℕ))
        * (a.eval (ambTheta F)
          * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F 𝔰)) (ambTheta F))
      = (∏ j : Fin r, ambGammaF F ((𝔰 j : ℕ)))
        * (a.eval (ambTheta F) * ambInfHom F (ζ_A F 𝔰)) := by
  have hlen : ((tupleListH F 𝔰).reverse).length = r := by
    rw [List.length_reverse, tupleListH_length]
  have hmem : ∀ j : Fin ((tupleListH F 𝔰).reverse).length, (j : ℕ) < r := by
    intro j
    have h1 := j.isLt
    omega
  let 𝔰' : Fin ((tupleListH F 𝔰).reverse).length → ℕ+ := fun j => 𝔰 ⟨j.1, hmem j⟩
  have hne : (tupleListH F 𝔰).reverse ≠ [] := by
    intro h
    have h1 : ((tupleListH F 𝔰).reverse).length = 0 := by rw [h]; rfl
    rw [hlen] at h1
    omega
  have hQ : ∀ j : Fin ((tupleListH F 𝔰).reverse).length,
      (((tupleListH F 𝔰).reverse).get j).2
        = ((ambH F ((((tupleListH F 𝔰).reverse).get j).1) : Polynomial (Ambient F))
            : PowerSeries (Ambient F)) :=
    fun j => tupleListH_reverse_get_snd F 𝔰 j
  have hpos : ∀ j : Fin ((tupleListH F 𝔰).reverse).length,
      1 ≤ (((tupleListH F 𝔰).reverse).get j).1 := by
    intro j
    rw [tupleListH_reverse_get_fst F 𝔰 j]
    exact (𝔰 _).pos
  have hsupM : ∀ j : Fin ((tupleListH F 𝔰).reverse).length,
      (((tupleListH F 𝔰).reverse).get j).1 ≤ 2 * Nat.card F - 2 := by
    intro j
    rw [tupleListH_reverse_get_fst F 𝔰 j]
    exact hsup _
  have h𝔰' : ∀ j : Fin ((tupleListH F 𝔰).reverse).length,
      ((𝔰' j : ℕ)) = (((tupleListH F 𝔰).reverse).get (Fin.rev j)).1 := by
    intro j
    rw [tupleListH_reverse_get_fst F 𝔰 (Fin.rev j)]
    show ((𝔰 ⟨j.1, hmem j⟩ : ℕ)) = _
    congr 1
    congr 1
    apply Fin.ext
    simp only [Fin.val_cast, Fin.rev_rev]
  have h𝔰'q : ∀ j : Fin ((tupleListH F 𝔰).reverse).length, (𝔰' j : ℕ) ≤ 2 * Nat.card F - 2 :=
    fun j => hsup _
  have hb := bridgeP_mul F ((tupleListH F 𝔰).reverse) hne hQ hpos hsupM 𝔰' h𝔰' h𝔰'q a
  have hsum : (∑ j : Fin ((tupleListH F 𝔰).reverse).length, ((𝔰' j : ℕ)))
      = ∑ j : Fin r, ((𝔰 j : ℕ)) := by
    refine Fintype.sum_equiv (Fin.castOrderIso hlen).toEquiv
      (fun j : Fin ((tupleListH F 𝔰).reverse).length => ((𝔰' j : ℕ)))
      (fun j : Fin r => ((𝔰 j : ℕ))) (fun j => ?_)
    rfl
  have hprodΓ : (∏ j : Fin ((tupleListH F 𝔰).reverse).length, ambGammaF F (𝔰' j : ℕ))
      = ∏ j : Fin r, ambGammaF F (𝔰 j : ℕ) := by
    refine Fintype.prod_equiv (Fin.castOrderIso hlen).toEquiv
      (fun j : Fin ((tupleListH F 𝔰).reverse).length => ambGammaF F (𝔰' j : ℕ))
      (fun j : Fin r => ambGammaF F (𝔰 j : ℕ)) (fun j => ?_)
    rfl
  have hzeta : ζ_A F 𝔰' = ζ_A F 𝔰 := by
    refine ζ_A_eq_of_reindex F hlen 𝔰' 𝔰 (fun i => ?_)
    exact Subtype.ext rfl
  have hseries : tmL (Nat.card F) (ambOmega F) (tupleListHP F 𝔰)
      = atLrGen (Nat.card F) (ambOmega F) ((tupleListH F 𝔰).reverse) := by
    rw [tmL_eq_atLrGen_suffixList]
    simp only [suffixList, tmCoe_tupleListHP]
  rw [hsum, hprodΓ, hzeta] at hb
  rw [hseries]
  exact hb

/-- The bridge (4.2) for a `Fin`-indexed tuple, without the extra factor. -/
theorem bridgeP_tuple {r : ℕ} (𝔰 : Fin r → ℕ+) (hr : 0 < r)
    (hsup : ∀ j : Fin r, (𝔰 j : ℕ) ≤ 2 * Nat.card F - 2) :
    (ambPiTilde F) ^ (∑ j : Fin r, (𝔰 j : ℕ))
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F 𝔰)) (ambTheta F)
      = (∏ j : Fin r, ambGammaF F ((𝔰 j : ℕ))) * ambInfHom F (ζ_A F 𝔰) := by
  have h := bridgeP_tuple_mul F 𝔰 hr hsup (1 : Polynomial (Ambient F))
  simpa using h

end TupleForm

end ZagierHoffmanPositiveChar
