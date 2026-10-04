import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarDef
import Submission.Work.Diff.STE.B3.VarCoef.mulOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.pdOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.commMulPd
import Submission.Work.Diff.STE.B3.VarCoef.isOrd_commOp_iterate
import Submission.Work.Diff.STE.B3.VarCoef.isOrd_pow_sub

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `POpStar c c' A B k` is `POp c' c (varLapStarOp A B) k`. -/
theorem POpStar_eq_POp (c c' : (ι → ℝ) → ℝ) (A : ι → ι → (ι → ℝ) → ℝ)
    (B : ι → (ι → ℝ) → ℝ) (k : ℕ) :
    POpStar c c' A B k = POp c' c (varLapStarOp A B) k := rfl

/-- The pointwise decomposition of `POp c c' D k - POp c' c E k`. -/
theorem POp_sub_POp_apply (c c' : (ι → ℝ) → ℝ) (D E : Op ι) (k : ℕ)
    (f : (ι → ℝ) → ℂ) :
    (POp c c' D k - POp c' c E k) f
      = (((compOp (mulOp c') (commOp (D^[k]) (mulOp c))
            - compOp (mulOp c) (commOp (D^[k]) (mulOp c')))
          + compOp (compOp (mulOp c) (D^[k] - E^[k])) (mulOp c')) f) := by
  funext x
  simp only [POp, compOp_apply, commOp_apply, Pi.sub_apply, Pi.add_apply, mulOp]
  ring

/-- `[M_m, M_{m'}] = 0` (as operators, pointwise). -/
theorem commOp_mulOp_mulOp_zero {m m' : (ι → ℝ) → ℝ} (f : (ι → ℝ) → ℂ) :
    commOp (mulOp m) (mulOp m') f = (0 : Op ι) f := by
  funext x
  simp only [commOp_apply, mulOp, Pi.sub_apply, Pi.zero_apply]
  ring

/-- `[M_m, ∂_a] = -M_{∂_a m}` on smooth periodic functions. -/
theorem commOp_mulOp_pdOp_eq_neg {m : (ι → ℝ) → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (a : ι)
    (f : (ι → ℝ) → ℂ) (hf : SmoothPer f) :
    commOp (mulOp m) (pdOp a) f = (-(mulOp (Work.Diff.STE.pdR a m))) f := by
  rw [commMulPd m hm a f hf]
  rfl

/-- `commOp D^[k] M_m = - commOp M_m D^[k]`. -/
theorem commOp_pow_mulOp_eq_neg (D : Op ι) (m : (ι → ℝ) → ℝ) (k : ℕ)
    (f : (ι → ℝ) → ℂ) :
    commOp (D^[k]) (mulOp m) f = -(commOp (mulOp m) (D^[k]) f) := by
  simp only [commOp_apply, Pi.neg_apply]
  ring

/-- **`varLap` commutator certificate against a multiplier**:  `varLapOp A B` has order `2`, and its
commutator with `mulOp c` has order `1`. -/
theorem varLapOp_isCommOrd_mulOp (c : (ι → ℝ) → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcp : Work.Diff.STE.Periodic1 c) (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a)) :
    ∃ C Cl : ℤ → ℝ, IsCommOrd (mulOp c) 2 C Cl (varLapOp A B) := by
  classical
  obtain ⟨Cc, hCc⟩ := mulOp_isOrd c hc hcp
  choose CA hCA using fun (a : ι) (b : ι) => mulOp_isOrd (A a b) (hA a b) (hAp a b)
  choose CB hCB using fun (a : ι) => mulOp_isOrd (B a) (hB a) (hBp a)
  choose Cp hCp using fun (i : ι) => pdOp_isOrd i
  choose Cpg hCpg using fun (i : ι) =>
    mulOp_isOrd (Work.Diff.STE.pdR i c) (pdR_contDiff hc i) (pdR_periodic hcp i)
  exact ⟨_, _, varLap_isCommOrd_exp (mulOp c) hCc.lin hCc.pres A B
    CA (fun _ _ => fun _ => 0) CB (fun _ => fun _ => 0) Cp Cpg
    (fun a b => hCA a b)
    (fun a b => IsOrd.congr (T := (0 : Op ι)) (IsOrd.zero' (-1))
      (fun f _ => (commOp_mulOp_mulOp_zero (m := c) (m' := A a b) f).symm))
    (fun a => hCB a)
    (fun a => IsOrd.congr (T := (0 : Op ι)) (IsOrd.zero' (-1))
      (fun f _ => (commOp_mulOp_mulOp_zero (m := c) (m' := B a) f).symm))
    (fun i => hCp i)
    (fun i => IsOrd.congr (T := -(mulOp (Work.Diff.STE.pdR i c))) (IsOrd.neg (hCpg i))
      (fun f hf => (commOp_mulOp_pdOp_eq_neg hc i f hf).symm))⟩

/-- `[M_m, ∂_a]` has order `0` (for smooth `1`-periodic `m`). -/
theorem commOp_mulOp_pdOp_isOrd {m : (ι → ℝ) → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hmp : Work.Diff.STE.Periodic1 m) (a : ι) :
    ∃ C : ℤ → ℝ, IsOrd 0 C (commOp (mulOp m) (pdOp a)) := by
  obtain ⟨C, hC⟩ := mulOp_isOrd (Work.Diff.STE.pdR a m) (pdR_contDiff hm a) (pdR_periodic hmp a)
  exact ⟨C, IsOrd.congr (T := -(mulOp (Work.Diff.STE.pdR a m))) (IsOrd.neg hC)
    (fun f hf => (commOp_mulOp_pdOp_eq_neg hm a f hf).symm)⟩

/-- `[M_m, ∂_a∂_b]` has order `1`: Leibniz on the composition `∂_a ∘ ∂_b`, both commutators
`[M_m, ∂_a]`, `[M_m, ∂_b]` being of order `0`. -/
theorem commOp_mulOp_pdOp_pdOp_isOrd {m : (ι → ℝ) → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hmp : Work.Diff.STE.Periodic1 m) (a b : ι) :
    ∃ C : ℤ → ℝ, IsOrd 1 C (commOp (mulOp m) (compOp (pdOp a) (pdOp b))) := by
  obtain ⟨Cm, hCm⟩ := mulOp_isOrd m hm hmp
  obtain ⟨C1, hC1⟩ := commOp_mulOp_pdOp_isOrd hm hmp a
  obtain ⟨C2, hC2⟩ := commOp_mulOp_pdOp_isOrd hm hmp b
  obtain ⟨Ca, hCa⟩ := pdOp_isOrd a
  obtain ⟨Cb, hCb⟩ := pdOp_isOrd b
  have hp1 : ∃ C : ℤ → ℝ, IsOrd 1 C (compOp (commOp (mulOp m) (pdOp a)) (pdOp b)) :=
    ⟨_, IsOrd.mono_d (d := 1) (d' := 0 + 1)
      (IsOrd.comp (T := commOp (mulOp m) (pdOp a)) (U := pdOp b) hC1 hCb) (by omega)⟩
  have hp2 : ∃ C : ℤ → ℝ, IsOrd 1 C (compOp (pdOp a) (commOp (mulOp m) (pdOp b))) :=
    ⟨_, IsOrd.mono_d (d := 1) (d' := 1 + 0)
      (IsOrd.comp (T := pdOp a) (U := commOp (mulOp m) (pdOp b)) hCa hC2) (by omega)⟩
  obtain ⟨D1, hD1⟩ := hp1
  obtain ⟨D2, hD2⟩ := hp2
  refine ⟨_, IsOrd.congr (T := compOp (commOp (mulOp m) (pdOp a)) (pdOp b)
      + compOp (pdOp a) (commOp (mulOp m) (pdOp b))) (IsOrd.add hD1 hD2) (fun f hf => ?_)⟩
  exact (commOp_compOp_apply hCa.lin hCm.pres hCb.pres hf).symm

/-- `varLap A B - varLapStar A B` is the negative of the sum of the commutators
`[M_{A a b}, ∂_a∂_b]` and `[M_{B a}, ∂_a]`. -/
theorem varLap_sub_star_eq (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (f : (ι → ℝ) → ℂ) :
    (varLapOp A B - varLapStarOp A B) f
      = -(((∑ a, ∑ b, commOp (mulOp (A a b)) (compOp (pdOp a) (pdOp b)))
          + (∑ a, commOp (mulOp (B a)) (pdOp a))) f) := by
  funext x
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply, varLapOp, varLapStarOp, varLap, varLapStar,
    compOp_apply, commOp_apply, mulOp, pdOp, Finset.sum_apply]
  simp only [Finset.sum_sub_distrib]
  have hmulOp : ∀ (m' : (ι → ℝ) → ℝ) (g : (ι → ℝ) → ℂ),
      mulOp m' g = fun y => ((m' y : ℝ) : ℂ) * g y := fun _ _ => rfl
  simp only [hmulOp]
  ring

/-- **`varLap A B - varLapStar A B` has order `1`** (the leading second-order terms cancel). -/
theorem varLap_sub_varLapStar_isOrd_local (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a)) :
    ∃ C : ℤ → ℝ, IsOrd 1 C (varLapOp A B - varLapStarOp A B) := by
  classical
  have hT1 : ∃ C : ℤ → ℝ, IsOrd 1 C
      (∑ a, ∑ b, commOp (mulOp (A a b)) (compOp (pdOp a) (pdOp b))) := by
    have hinner : ∀ a : ι, ∃ C : ℤ → ℝ, IsOrd 1 C
        (∑ b, commOp (mulOp (A a b)) (compOp (pdOp a) (pdOp b))) := by
      intro a
      choose C hC using fun b : ι => commOp_mulOp_pdOp_pdOp_isOrd (hA a b) (hAp a b) a b
      exact ⟨fun t => (Fintype.card ι : ℝ) * ∑ b, C b t,
        IsOrd.sum Finset.univ (fun b => commOp (mulOp (A a b)) (compOp (pdOp a) (pdOp b))) C
          (fun b _ => hC b)⟩
    choose C hC using hinner
    exact ⟨fun t => (Fintype.card ι : ℝ) * ∑ a, C a t,
      IsOrd.sum Finset.univ (fun a => ∑ b, commOp (mulOp (A a b)) (compOp (pdOp a) (pdOp b))) C
        (fun a _ => hC a)⟩
  have hT2 : ∃ C : ℤ → ℝ, IsOrd 1 C (∑ a, commOp (mulOp (B a)) (pdOp a)) := by
    choose C hC using fun a : ι => commOp_mulOp_pdOp_isOrd (hB a) (hBp a) a
    exact ⟨fun t => (Fintype.card ι : ℝ) * ∑ a, C a t,
      IsOrd.sum Finset.univ (fun a => commOp (mulOp (B a)) (pdOp a)) C
        (fun a _ => IsOrd.mono_d (d := 1) (d' := 0) (hC a) (by norm_num))⟩
  obtain ⟨C1, hC1⟩ := hT1
  obtain ⟨C2, hC2⟩ := hT2
  refine ⟨_, IsOrd.congr (T := -((∑ a, ∑ b, commOp (mulOp (A a b)) (compOp (pdOp a) (pdOp b)))
        + (∑ a, commOp (mulOp (B a)) (pdOp a)))) (IsOrd.neg (IsOrd.add hC1 hC2))
    (fun f _ => (varLap_sub_star_eq A B f).symm)⟩

/-- **Order-calculus core of `POp_sub_star_isOrd`.**  Given the order certificates for the two
multipliers, for the difference `D^k - E^k` (`D = varLapOp A B`, `E = varLapStarOp A B`) and for
the two commutators `[M_c, D^k]`, `[M_c', D^k]`, the operator
`POp c c' D k - POpStar c c' A B k` has order `2k - 1`. -/
theorem POp_sub_star_isOrd_of_orders (c c' : (ι → ℝ) → ℝ) (A : ι → ι → (ι → ℝ) → ℝ)
    (B : ι → (ι → ℝ) → ℝ) (k : ℕ)
    (hCc : ∃ C : ℤ → ℝ, IsOrd 0 C (mulOp c))
    (hCc' : ∃ C : ℤ → ℝ, IsOrd 0 C (mulOp c'))
    (hPde : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      ((varLapOp A B)^[k] - (varLapStarOp A B)^[k]))
    (hC1 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C (commOp (mulOp c) ((varLapOp A B)^[k])))
    (hC2 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C (commOp (mulOp c') ((varLapOp A B)^[k]))) :
    ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (POp c c' (varLapOp A B) k - POpStar c c' A B k) := by
  classical
  obtain ⟨Cc, hCc⟩ := hCc
  obtain ⟨Cc', hCc'⟩ := hCc'
  obtain ⟨Cde, hde⟩ := hPde
  obtain ⟨C1, hC1⟩ := hC1
  obtain ⟨C2, hC2⟩ := hC2
  -- `commOp D^[k] M_m = - commOp M_m D^[k]`
  obtain ⟨Cn1, hneg1⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (commOp ((varLapOp A B)^[k]) (mulOp c)) :=
    ⟨C1, IsOrd.congr (T := -(commOp (mulOp c) ((varLapOp A B)^[k]))) (IsOrd.neg hC1)
      (fun f _ => (commOp_pow_mulOp_eq_neg (varLapOp A B) c k f).symm)⟩
  obtain ⟨Cn2, hneg2⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (commOp ((varLapOp A B)^[k]) (mulOp c')) :=
    ⟨C2, IsOrd.congr (T := -(commOp (mulOp c') ((varLapOp A B)^[k]))) (IsOrd.neg hC2)
      (fun f _ => (commOp_pow_mulOp_eq_neg (varLapOp A B) c' k f).symm)⟩
  obtain ⟨CA1, hA1⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (mulOp c') (commOp ((varLapOp A B)^[k]) (mulOp c))) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1) (d' := 0 + (2 * (k : ℤ) - 1))
      (IsOrd.comp (T := mulOp c') (U := commOp ((varLapOp A B)^[k]) (mulOp c)) hCc' hneg1)
      (by omega)⟩
  obtain ⟨CB1, hB1⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (mulOp c) (commOp ((varLapOp A B)^[k]) (mulOp c'))) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1) (d' := 0 + (2 * (k : ℤ) - 1))
      (IsOrd.comp (T := mulOp c) (U := commOp ((varLapOp A B)^[k]) (mulOp c')) hCc hneg2)
      (by omega)⟩
  obtain ⟨CAB, hAB⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (mulOp c') (commOp ((varLapOp A B)^[k]) (mulOp c))
        - compOp (mulOp c) (commOp ((varLapOp A B)^[k]) (mulOp c'))) :=
    ⟨_, IsOrd.sub hA1 hB1⟩
  obtain ⟨Cmid, hmid⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (mulOp c) ((varLapOp A B)^[k] - (varLapStarOp A B)^[k])) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1) (d' := 0 + (2 * (k : ℤ) - 1))
      (IsOrd.comp (T := mulOp c) (U := (varLapOp A B)^[k] - (varLapStarOp A B)^[k]) hCc hde)
      (by omega)⟩
  obtain ⟨C3, h3⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (compOp (mulOp c) ((varLapOp A B)^[k] - (varLapStarOp A B)^[k])) (mulOp c')) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1) (d' := (2 * (k : ℤ) - 1) + 0)
      (IsOrd.comp (T := compOp (mulOp c) ((varLapOp A B)^[k] - (varLapStarOp A B)^[k]))
        (U := mulOp c') hmid hCc') (by omega)⟩
  exact ⟨_, IsOrd.congr (T := (compOp (mulOp c') (commOp ((varLapOp A B)^[k]) (mulOp c))
        - compOp (mulOp c) (commOp ((varLapOp A B)^[k]) (mulOp c')))
        + compOp (compOp (mulOp c) ((varLapOp A B)^[k] - (varLapStarOp A B)^[k])) (mulOp c'))
    (IsOrd.add hAB h3) (fun f _ => by
      rw [POpStar_eq_POp]
      exact (POp_sub_POp_apply c c' (varLapOp A B) (varLapStarOp A B) k f).symm)⟩

theorem POp_sub_star_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k)
    {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ} {c c' : (ι → ℝ) → ℝ}
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcp : Work.Diff.STE.Periodic1 c)
    (hc' : ContDiff ℝ (⊤ : ℕ∞) c') (hc'p : Work.Diff.STE.Periodic1 c') :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C
      (Work.Diff.STE.B3.VarCoef.POp c c' (Work.Diff.STE.B3.VarCoef.varLapOp A B) k
        - Work.Diff.STE.B3.VarCoef.POpStar c c' A B k) := by
  classical
  obtain ⟨Cc, hCc⟩ := mulOp_isOrd c hc hcp
  obtain ⟨Cc', hCc'⟩ := mulOp_isOrd c' hc' hc'p
  obtain ⟨CD, CSD, hVLC⟩ := varLapOp_isCommOrd_mulOp c hc hcp A B hA hAp hB hBp
  obtain ⟨CD', CSD', hVLC'⟩ := varLapOp_isCommOrd_mulOp c' hc' hc'p A B hA hAp hB hBp
  obtain ⟨CDE, hDE⟩ := varLap_sub_varLapStar_isOrd_local A B hA hAp hB hBp
  -- `varLapStarOp A B = varLapOp A B - (varLapOp A B - varLapStarOp A B)`, hence of order `2`
  have hDE2 : ∃ C : ℤ → ℝ, IsOrd 2 C (varLapOp A B - varLapStarOp A B) :=
    ⟨CDE, IsOrd.mono_d (d := 2) (d' := 1) hDE (by norm_num)⟩
  obtain ⟨CE, hE⟩ : ∃ C : ℤ → ℝ, IsOrd 2 C (varLapStarOp A B) :=
    ⟨_, IsOrd.congr (T := varLapOp A B - (varLapOp A B - varLapStarOp A B))
      (IsOrd.sub hVLC.ord hDE2.choose_spec) (fun f _ => by
        funext x
        simp only [Pi.sub_apply]
        ring)⟩
  obtain ⟨Cde, hde⟩ := isOrd_pow_sub (D := varLapOp A B) (E := varLapStarOp A B) hVLC.ord hE hDE k
  obtain ⟨C1, hC1'⟩ := isOrd_commOp_iterate (D := varLapOp A B) (L := mulOp c)
    (CD := CD) (δ := 1) (Cδ := CSD) hVLC.ord hVLC.comm hCc.lin hCc.pres k
  obtain ⟨C2, hC2'⟩ := isOrd_commOp_iterate (D := varLapOp A B) (L := mulOp c')
    (CD := CD') (δ := 1) (Cδ := CSD') hVLC'.ord hVLC'.comm hCc'.lin hCc'.pres k
  have hC1 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (commOp (mulOp c) ((varLapOp A B)^[k])) :=
    ⟨C1, IsOrd.mono_d (d := 2 * (k : ℤ) - 1) (d' := 1 + 2 * (k : ℤ) - 2) hC1' (by omega)⟩
  have hC2 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (commOp (mulOp c') ((varLapOp A B)^[k])) :=
    ⟨C2, IsOrd.mono_d (d := 2 * (k : ℤ) - 1) (d' := 1 + 2 * (k : ℤ) - 2) hC2' (by omega)⟩
  exact POp_sub_star_isOrd_of_orders c c' A B k ⟨Cc, hCc⟩ ⟨Cc', hCc'⟩ ⟨Cde, hde⟩ hC1 hC2

end Work.Diff.STE.B3.VarCoef
