import Mathlib
import Submission.Work.Peluse.Holds.SwapDefs

namespace Work.Peluse.SwapA

open scoped BigOperators
open Finset

noncomputable section

/-! ## Reindexing the sums over the dilated windows `q k [M]`

`boxNormPow d (fun k => arithIcc (q k) M) S f` averages over the shift tuples
`h : (k : Fin d) → {x // x ∈ arithIcc (q k) M}`, while `pbox d q 0 M S f` averages over the raw
index tuples `Fin d → Fin M` (twice, with the second coordinate unused).  Since `arithIcc (q k) M`
is the image of `{1,…,M}` under `n ↦ q k * n` — a bijection for `q k ≠ 0`, and the constant map with
value `0` for `q k = 0` — the two sums differ by the multiplicity factor `#(arithIcc (q k) M) / M`
per slot, and a factor `M` per unused coordinate.  The lemmas below make this precise. -/

/-- The cube term at the shift pair `(a, b)`: `∑_x ∏_ω C^{|ω|} f (x + cornerShift a b ω)`. -/
def cubeSum (d : ℕ) (f : ℤ → ℂ) (a b : Fin d → ℤ) : ℂ :=
  ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω]) (f (x + cornerShift a b ω))

/-- **One slot.**  Summing over the dilated window `c[M]` (i.e. over the subtype of elements of
`arithIcc c M`) equals the multiplicity factor `#(c[M]) / M` times the sum over the raw index range
`Fin M`, the index `n` standing for the element `c * (n + 1)`.

For `c ≠ 0` the factor is `1` (`#(c[M]) = M`, and `n ↦ c(n+1)` is a bijection), for `c = 0` the
factor is `1 / M` (`#(0[M]) = 1` and the index map is constant). -/
lemma sum_subtype_arithIcc (c : ℤ) (M : ℕ) (hM : 1 ≤ M) (G : ℤ → ℂ) :
    (∑ x : {y : ℤ // y ∈ arithIcc c M}, G x.1)
      = ((arithIcc c M).card : ℂ) * (M : ℂ)⁻¹ * ∑ n : Fin M, G (c * (((n : ℕ) : ℤ) + 1)) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hM)
  by_cases hc : c = 0
  · subst hc
    have hfun : (fun n : ℕ => (0 : ℤ) * ((n : ℤ))) = fun _ => (0 : ℤ) := by funext n; simp
    have hne : (Finset.Icc 1 M).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.Icc_eq_empty_iff]; omega
    have hset : arithIcc 0 M = ({0} : Finset ℤ) := by
      rw [arithIcc, hfun, Finset.image_const hne]
    have hcard0 : (arithIcc 0 M).card = 1 := by rw [hset]; simp
    have hsum1 : (∑ x : {y : ℤ // y ∈ arithIcc 0 M}, G x.1) = G 0 := by
      rw [Finset.univ_eq_attach, Finset.sum_attach, hset, Finset.sum_singleton]
    rw [hsum1, hcard0, Nat.cast_one]
    rw [show (∑ n : Fin M, G (0 * (((n : ℕ) : ℤ) + 1))) = ∑ _n : Fin M, G 0 from
      Finset.sum_congr rfl (fun n _ => by norm_num)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [one_mul, ← mul_assoc, inv_mul_cancel₀ hM', one_mul]
  · have hcard : (arithIcc c M).card = M := BoxNormDilation.card_arithIcc hc M
    have hsum1 : (∑ x : {y : ℤ // y ∈ arithIcc c M}, G x.1)
        = ∑ n : Fin M, G (c * (((n : ℕ) : ℤ) + 1)) := by
      rw [Finset.univ_eq_attach, Finset.sum_attach, arithIcc]
      have hinj : Set.InjOn (fun n : ℕ => c * ((n : ℤ))) (↑(Finset.Icc 1 M) : Set ℕ) := by
        intro a ha b hb hab
        have h2 : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := mul_left_cancel₀ hc hab
        exact Int.ofNat_inj.mp h2
      rw [Finset.sum_image hinj]
      refine (Finset.sum_bij (fun (n : Fin M) (_ : n ∈ Finset.univ) => n.1 + 1) ?_ ?_ ?_ ?_).symm
      · intro a ha
        rw [Finset.mem_Icc]; have := a.2; omega
      · intro a₁ ha₁ a₂ ha₂ h
        exact Fin.ext (by omega)
      · intro b hb
        obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
        refine ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        show b - 1 + 1 = b
        omega
      · intro a ha
        have hcast : (((a.1 + 1 : ℕ)) : ℤ) = (((a : ℕ) : ℤ) + 1) := by push_cast; ring
        rw [hcast]
    rw [hsum1, hcard]
    rw [mul_inv_cancel₀ hM', one_mul]

/-- **All slots.**  The same reindexing for a whole tuple of slots: summing over
`(k : Fin d) → {x // x ∈ arithIcc (q k) M}` equals the product of the per-slot multiplicity factors
`∏ k, #(q k [M]) / M` times the sum over the raw index tuple `(k : Fin d) → Fin M`. -/
theorem sum_pi_arithIcc (M : ℕ) (hM : 1 ≤ M) :
    ∀ (d : ℕ) (q : Fin d → ℤ) (F : (Fin d → ℤ) → ℂ),
      (∑ h : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k) M}, F (fun k => (h k).1))
        = (∏ k, ((arithIcc (q k) M).card : ℂ) * (M : ℂ)⁻¹)
            * ∑ n : (k : Fin d) → Fin M, F (fun k => q k * (((n k : ℕ) : ℤ) + 1)) := by
  intro d
  induction d with
  | zero =>
    intro q F
    have hconst : ∀ h : (k : Fin 0) → {x : ℤ // x ∈ arithIcc (q k) M},
        F (fun k => (h k).1) = F (fun _ : Fin 0 => 0) := by
      intro h; congr 1; funext k; exact k.elim0
    have hconst2 : ∀ n : (k : Fin 0) → Fin M,
        F (fun k => q k * (((n k : ℕ) : ℤ) + 1)) = F (fun _ : Fin 0 => 0) := by
      intro n; congr 1; funext k; exact k.elim0
    rw [show (∑ h : (k : Fin 0) → {x : ℤ // x ∈ arithIcc (q k) M}, F (fun k => (h k).1))
          = F (fun _ : Fin 0 => 0) from by
        rw [Finset.sum_congr rfl (fun h _ => hconst h), Finset.sum_const, Finset.card_univ,
          Fintype.card_pi, Finset.univ_eq_empty, Finset.prod_empty, one_smul],
        show (∑ n : (k : Fin 0) → Fin M, F (fun k => q k * (((n k : ℕ) : ℤ) + 1)))
          = F (fun _ : Fin 0 => 0) from by
        rw [Finset.sum_congr rfl (fun n _ => hconst2 n), Finset.sum_const, Finset.card_univ,
          Fintype.card_pi, Finset.univ_eq_empty, Finset.prod_empty, one_smul],
        Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  | succ d ih =>
    intro q F
    have hL : (∑ h : (k : Fin (d + 1)) → {x : ℤ // x ∈ arithIcc (q k) M}, F (fun k => (h k).1))
        = ∑ a : {x : ℤ // x ∈ arithIcc (q 0) M},
            ∑ hs : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k.succ) M},
              F (Fin.cons a.1 (fun i => (hs i).1)) := by
      rw [(Equiv.sum_comp (Fin.consEquiv (fun k : Fin (d + 1) => {x : ℤ // x ∈ arithIcc (q k) M}))
            (fun h => F (fun k => (h k).1))).symm]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun hs _ => ?_))
      congr 1
      funext k
      cases k using Fin.cases <;> simp [Fin.consEquiv_apply]
    have hsingle : (∑ a : {x : ℤ // x ∈ arithIcc (q 0) M},
          ∑ hs : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k.succ) M},
            F (Fin.cons a.1 (fun i => (hs i).1)))
        = ((arithIcc (q 0) M).card : ℂ) * (M : ℂ)⁻¹ *
            ∑ n0 : Fin M, ∑ hs : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k.succ) M},
              F (Fin.cons (q 0 * (((n0 : ℕ) : ℤ) + 1)) (fun i => (hs i).1)) :=
      sum_subtype_arithIcc (q 0) M hM
        (fun y => ∑ hs : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k.succ) M},
          F (Fin.cons y (fun i => (hs i).1)))
    have hih : ∀ n0 : Fin M,
        (∑ hs : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k.succ) M},
            F (Fin.cons (q 0 * (((n0 : ℕ) : ℤ) + 1)) (fun i => (hs i).1)))
        = (∏ k : Fin d, ((arithIcc (q k.succ) M).card : ℂ) * (M : ℂ)⁻¹) *
            ∑ n' : (k : Fin d) → Fin M,
              F (Fin.cons (q 0 * (((n0 : ℕ) : ℤ) + 1))
                (fun i => q i.succ * (((n' i : ℕ) : ℤ) + 1))) :=
      fun n0 => ih (fun i : Fin d => q i.succ)
        (fun b => F (Fin.cons (q 0 * (((n0 : ℕ) : ℤ) + 1)) b))
    have hR : (∑ n : (k : Fin (d + 1)) → Fin M, F (fun k => q k * (((n k : ℕ) : ℤ) + 1)))
        = ∑ n0 : Fin M, ∑ n' : (k : Fin d) → Fin M,
            F (Fin.cons (q 0 * (((n0 : ℕ) : ℤ) + 1))
              (fun i => q i.succ * (((n' i : ℕ) : ℤ) + 1))) := by
      rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Fin M))
            (fun n => F (fun k => q k * (((n k : ℕ) : ℤ) + 1)))).symm]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun n0 _ => Finset.sum_congr rfl (fun n' _ => ?_))
      congr 1
      funext k
      cases k using Fin.cases <;> simp [Fin.consEquiv_apply]
    rw [hL, hsingle, hR]
    rw [Finset.sum_congr rfl (fun n0 _ => hih n0)]
    rw [← Finset.mul_sum]
    rw [Fin.prod_univ_succ]
    ring

/-- The double (both shift tuples) version of `sum_pi_arithIcc`. -/
lemma sum_pi_arithIcc_two (d : ℕ) (q : Fin d → ℤ) (M : ℕ) (hM : 1 ≤ M)
    (H : (Fin d → ℤ) → (Fin d → ℤ) → ℂ) :
    (∑ h : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k) M},
        ∑ h' : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k) M},
          H (fun k => (h k).1) (fun k => (h' k).1))
      = (∏ k, ((arithIcc (q k) M).card : ℂ) * (M : ℂ)⁻¹)
          * (∏ k, ((arithIcc (q k) M).card : ℂ) * (M : ℂ)⁻¹)
          * ∑ n : (k : Fin d) → Fin M, ∑ n' : (k : Fin d) → Fin M,
              H (fun k => q k * (((n k : ℕ) : ℤ) + 1))
                (fun k => q k * (((n' k : ℕ) : ℤ) + 1)) := by
  have h1 : (∑ h : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k) M},
        ∑ h' : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k) M},
          H (fun k => (h k).1) (fun k => (h' k).1))
      = (∏ k, ((arithIcc (q k) M).card : ℂ) * (M : ℂ)⁻¹)
          * ∑ n : (k : Fin d) → Fin M, ∑ h' : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k) M},
              H (fun k => q k * (((n k : ℕ) : ℤ) + 1)) (fun k => (h' k).1) :=
    sum_pi_arithIcc M hM d q
      (fun a => ∑ h' : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k) M}, H a (fun k => (h' k).1))
  have h2 : (∑ n : (k : Fin d) → Fin M,
        ∑ h' : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k) M},
          H (fun k => q k * (((n k : ℕ) : ℤ) + 1)) (fun k => (h' k).1))
      = (∏ k, ((arithIcc (q k) M).card : ℂ) * (M : ℂ)⁻¹)
          * ∑ n : (k : Fin d) → Fin M, ∑ n' : (k : Fin d) → Fin M,
              H (fun k => q k * (((n k : ℕ) : ℤ) + 1))
                (fun k => q k * (((n' k : ℕ) : ℤ) + 1)) := by
    have h2a : ∀ n : (k : Fin d) → Fin M,
        (∑ h' : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k) M},
          H (fun k => q k * (((n k : ℕ) : ℤ) + 1)) (fun k => (h' k).1))
        = (∏ k, ((arithIcc (q k) M).card : ℂ) * (M : ℂ)⁻¹)
            * ∑ n' : (k : Fin d) → Fin M,
                H (fun k => q k * (((n k : ℕ) : ℤ) + 1))
                  (fun k => q k * (((n' k : ℕ) : ℤ) + 1)) :=
      fun n => sum_pi_arithIcc M hM d q
        (fun b => H (fun k => q k * (((n k : ℕ) : ℤ) + 1)) b)
    have h2b : (∑ n : (k : Fin d) → Fin M,
          ∑ h' : (k : Fin d) → {x : ℤ // x ∈ arithIcc (q k) M},
            H (fun k => q k * (((n k : ℕ) : ℤ) + 1)) (fun k => (h' k).1))
        = ∑ n : (k : Fin d) → Fin M, (∏ k, ((arithIcc (q k) M).card : ℂ) * (M : ℂ)⁻¹)
            * ∑ n' : (k : Fin d) → Fin M,
                H (fun k => q k * (((n k : ℕ) : ℤ) + 1))
                  (fun k => q k * (((n' k : ℕ) : ℤ) + 1)) :=
      Finset.sum_congr rfl (fun n _ => h2a n)
    rw [h2b, ← Finset.mul_sum]
  rw [h1, h2]
  ring

/-- The equivalence `(Fin d → Fin M) × (Fin d → Fin M) ≃ (Fin d → Fin M × Fin M)` whose two
components are the two coordinates. -/
def prodPiEquiv (d M : ℕ) : ((Fin d → Fin M) × (Fin d → Fin M)) ≃ (Fin d → Fin M × Fin M) where
  toFun g := fun i => (g.1 i, g.2 i)
  invFun f := (fun i => (f i).1, fun i => (f i).2)
  left_inv g := by cases g; rfl
  right_inv f := by funext i; rfl

/-- **Collapsing an unused coordinate.**  In `pboxSum` the second coordinate of each slot index
`m : Fin M × Fin M` never enters; summing over `Fin d → Fin M × Fin M` therefore costs a factor
`(M^d)` per coordinate. -/
lemma sum_pi_prod_fst (d M : ℕ) (G : (Fin d → ℤ) → ℂ) :
    (∑ h : Fin d → Fin M × Fin M, G (fun k => ((((h k).1 : Fin M) : ℕ) : ℤ)))
      = (M : ℂ)^d * ∑ n : Fin d → Fin M, G (fun k => (((n k : Fin M) : ℕ) : ℤ)) := by
  rw [(Equiv.sum_comp (prodPiEquiv d M)
        (fun h : Fin d → Fin M × Fin M => G (fun k => ((((h k).1 : Fin M) : ℕ) : ℤ)))).symm]
  simp only [prodPiEquiv, Equiv.coe_fn_mk]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ g1 : Fin d → Fin M,
      (∑ _g2 : Fin d → Fin M, G (fun k => ((((g1 k : Fin M)) : ℕ) : ℤ)))
        = (M : ℂ)^d * G (fun k => ((((g1 k : Fin M)) : ℕ) : ℤ)) := by
    intro g1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow]
  have hcong : (∑ g1 : Fin d → Fin M, ∑ _g2 : Fin d → Fin M,
        G (fun k => ((((g1 k : Fin M)) : ℕ) : ℤ)))
      = (M : ℂ)^d * ∑ g1 : Fin d → Fin M, G (fun k => ((((g1 k : Fin M)) : ℕ) : ℤ)) := by
    rw [Finset.sum_congr rfl (fun g1 _ => hinner g1), Finset.mul_sum]
  exact hcong

/-- The double version of `sum_pi_prod_fst`. -/
lemma sum_prod_fst_two (d M : ℕ) (H : (Fin d → ℤ) → (Fin d → ℤ) → ℂ) :
    (∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
        H (fun k => ((((h k).1 : Fin M) : ℕ) : ℤ)) (fun k => ((((h' k).1 : Fin M) : ℕ) : ℤ)))
      = (M : ℂ)^d * (M : ℂ)^d *
        ∑ n : Fin d → Fin M, ∑ n' : Fin d → Fin M,
          H (fun k => (((n k : Fin M) : ℕ) : ℤ)) (fun k => (((n' k : Fin M) : ℕ) : ℤ)) := by
  have h1 : (∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
        H (fun k => ((((h k).1 : Fin M) : ℕ) : ℤ)) (fun k => ((((h' k).1 : Fin M) : ℕ) : ℤ)))
      = (M : ℂ)^d * ∑ n : Fin d → Fin M, ∑ h' : Fin d → Fin M × Fin M,
          H (fun k => ((((n k : Fin M)) : ℕ) : ℤ)) (fun k => ((((h' k).1 : Fin M) : ℕ) : ℤ)) :=
    sum_pi_prod_fst d M (fun a => ∑ h' : Fin d → Fin M × Fin M,
      H a (fun k => ((((h' k).1 : Fin M) : ℕ) : ℤ)))
  have h2 : (∑ n : Fin d → Fin M, ∑ h' : Fin d → Fin M × Fin M,
          H (fun k => ((((n k : Fin M)) : ℕ) : ℤ)) (fun k => ((((h' k).1 : Fin M) : ℕ) : ℤ)))
      = (M : ℂ)^d * ∑ n : Fin d → Fin M, ∑ n' : Fin d → Fin M,
          H (fun k => ((((n k : Fin M)) : ℕ) : ℤ)) (fun k => ((((n' k : Fin M)) : ℕ) : ℤ)) := by
    have h2a : ∀ n : Fin d → Fin M,
        (∑ h' : Fin d → Fin M × Fin M,
          H (fun k => ((((n k : Fin M)) : ℕ) : ℤ)) (fun k => ((((h' k).1 : Fin M) : ℕ) : ℤ)))
        = (M : ℂ)^d * ∑ n' : Fin d → Fin M,
            H (fun k => ((((n k : Fin M)) : ℕ) : ℤ)) (fun k => ((((n' k : Fin M)) : ℕ) : ℤ)) :=
      fun n => sum_pi_prod_fst d M (fun b => H (fun k => ((((n k : Fin M)) : ℕ) : ℤ)) b)
    have h2b : (∑ n : Fin d → Fin M, ∑ h' : Fin d → Fin M × Fin M,
          H (fun k => ((((n k : Fin M)) : ℕ) : ℤ)) (fun k => ((((h' k).1 : Fin M) : ℕ) : ℤ)))
        = ∑ n : Fin d → Fin M, (M : ℂ)^d * ∑ n' : Fin d → Fin M,
            H (fun k => ((((n k : Fin M)) : ℕ) : ℤ)) (fun k => ((((n' k : Fin M)) : ℕ) : ℤ)) :=
      Finset.sum_congr rfl (fun n _ => h2a n)
    rw [h2b, ← Finset.mul_sum]
  rw [h1, h2]
  ring

/-- The raw form of `boxSumPow`: the cube sum over the two shift tuples. -/
lemma boxSumPow_eq_raw (d : ℕ) (Q : Fin d → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    boxSumPow d Q S f
      = (S.card : ℂ)⁻¹ * (∏ k, ((Q k).card : ℂ)⁻¹) * (∏ k, ((Q k).card : ℂ)⁻¹)
        * ∑ h : (k : Fin d) → {x : ℤ // x ∈ Q k}, ∑ h' : (k : Fin d) → {x : ℤ // x ∈ Q k},
            cubeSum d f (fun k => (h k).1) (fun k => (h' k).1) := rfl

/-- The raw form of `pboxSum`. -/
lemma pboxSum_eq_raw (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) :
    LadderP.Swap.pboxSum d q₁ q₂ M S f
      = (S.card : ℂ)⁻¹ * (((M : ℂ)^4)⁻¹)^d
        * ∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
            cubeSum d f (fun k => LadderP.Swap.pdir (q₁ k) (q₂ k) (h k))
              (fun k => LadderP.Swap.pdir (q₁ k) (q₂ k) (h' k)) := rfl

/-- The scalar bookkeeping of the identity: the product of the per-slot multiplicity factors
`∏ k, #(q k [M]) / M` cancels the box-norm scaling `∏ k, #(q k [M])⁻¹` (twice), leaving `M^{-2d}`;
this matches the `pboxSum` scaling `(M^4)^{-d}` times the `(M^d)^2` of the collapsed coordinate. -/
lemma swap_scalar (d : ℕ) (M : ℕ) (Q : Fin d → Finset ℤ) (S : Finset ℤ) (T : ℂ)
    (hM : 1 ≤ M) (hcard : ∀ k, (Q k).card ≠ 0) :
    (S.card : ℂ)⁻¹ * (∏ k, ((Q k).card : ℂ)⁻¹) * (∏ k, ((Q k).card : ℂ)⁻¹)
        * ((∏ k, ((Q k).card : ℂ) * (M : ℂ)⁻¹) * (∏ k, ((Q k).card : ℂ) * (M : ℂ)⁻¹) * T)
      = (S.card : ℂ)⁻¹ * (((M : ℂ)^4)⁻¹)^d * ((M : ℂ)^d * (M : ℂ)^d * T) := by
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hM)
  have hP0 : (∏ k, ((Q k).card : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => by
      rw [Nat.cast_ne_zero]; exact hcard k)
  have hMd2 : (M : ℂ) ^ (d * 2) ≠ 0 := pow_ne_zero _ hM0
  rw [Finset.prod_inv_distrib]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp
  ring_nf
  rw [inv_pow, inv_pow]
  rw [show (M : ℂ) ^ (d * 4) = (M : ℂ) ^ (d * 2) * (M : ℂ) ^ (d * 2) by rw [← pow_add]; ring]
  rw [mul_inv]
  field_simp

/-- Raw multiset slots are Peluse's dilated windows (no hypothesis on `q`; for `q = 0` both sides are the all-zero-shift average). -/
theorem boxNormPow_eq_pbox_raw (d : ℕ) (q : Fin d → ℤ) (M : ℕ)
    (hM : 1 ≤ M) (S : Finset ℤ) (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow d (fun k => Work.Peluse.arithIcc (q k) M) S f =
      Work.Peluse.LadderP.Swap.pbox d q (fun _ => 0) M S f := by
  have hpdir : ∀ h : Fin d → Fin M × Fin M,
      (fun k => LadderP.Swap.pdir (q k) 0 (h k))
        = fun k => q k * (((((h k).1 : Fin M) : ℕ) : ℤ) + 1) := by
    intro h; funext k; simp [LadderP.Swap.pdir]
  have hR : (∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
        cubeSum d f (fun k => LadderP.Swap.pdir (q k) 0 (h k))
          (fun k => LadderP.Swap.pdir (q k) 0 (h' k)))
      = ∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
          cubeSum d f (fun k => q k * (((((h k).1 : Fin M) : ℕ) : ℤ) + 1))
            (fun k => q k * (((((h' k).1 : Fin M) : ℕ) : ℤ) + 1)) := by
    refine Finset.sum_congr rfl (fun h _ => ?_)
    refine Finset.sum_congr rfl (fun h' _ => ?_)
    rw [hpdir h, hpdir h']
  have hmain : boxSumPow d (fun k => arithIcc (q k) M) S f
      = LadderP.Swap.pboxSum d q (fun _ => 0) M S f := by
    rw [boxSumPow_eq_raw, sum_pi_arithIcc_two d q M hM (cubeSum d f)]
    rw [pboxSum_eq_raw, hR,
      sum_prod_fst_two d M
        (fun a b => cubeSum d f (fun k => q k * (a k + 1)) (fun k => q k * (b k + 1)))]
    exact swap_scalar d M (fun k => arithIcc (q k) M) S _ hM
      (fun k => Finset.card_ne_zero_of_mem (a := q k * ((1 : ℕ) : ℤ)) (by
        rw [arithIcc]
        exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM⟩, by push_cast; ring⟩))
  rw [boxNormPow, LadderP.Swap.pbox, hmain]

end

end Work.Peluse.SwapA
