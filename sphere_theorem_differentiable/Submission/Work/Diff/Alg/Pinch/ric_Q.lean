import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci tensor of Hamilton's reaction term

For an algebraic curvature tensor `R` (components `R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫` in an
orthonormal frame) the Ricci contraction of Hamilton's quadratic term
`Q(R)ᵢⱼₖₗ = ∑_{p,q} (Rᵢⱼₚq Rₖₗₚq + 2 Rᵢₚₖq Rⱼₚₗq − 2 Rᵢₚₗq Rⱼₚₖq)`
is twice the contraction of the Ricci tensor with `R`:

`ric (Q R) i j = 2 ∑_{p,q} ric R p q · R i p j q`.

Together with `ric R p q = ∑_k R k p k q` this is the `(0,2)`-tensor companion of the scalar
identity `scalAlg (Q R) = 2 |ric R|²` (`Work.Diff.Alg.Pinch.scalAlg_Q`); it is the "Ricci flow
evolution of the Ricci tensor in an Uhlenbeck frame" identity.

## Structure of the proof

Write `T₁ = ∑_{k,p,q} R_{kipq}R_{kjpq}`, `T₂ = ∑_{k,p,q} R_{kpkq}R_{ipjq}` and
`T₃ = ∑_{k,p,q} R_{kpjq}R_{ipkq}`.  Expanding `ric (Q R) i j` gives `T₁ + 2T₂ − 2T₃`, while
`∑_{p,q} ric R p q · R i p j q = T₂` (regrouping the three sums), so everything reduces to
`T₁ = 2T₃` — the `(i,j)`-entry of the index gymnastics already familiar from `scalAlg_Q`.

That identity is proved through the auxiliary sums
`S_A = ∑ R_{abi c}R_{abj c}`, `S_B = ∑ R_{aci b}R_{abj c}`, `S_D = ∑ R_{aci b}R_{acj b}` and
`W = ∑ R_{abj c}R_{iab c}`:

* the antisymmetrised Bianchi identity `R_{abcd} = R_{acbd} − R_{adbc}` (a consequence of the
  three symmetries) expands `T₁ = S_A − S_B − S_C + S_D` with `S_C = ∑ R_{abi c}R_{acj b}`;
* the reindexings `S_C = S_B` and `S_D = S_A` (exchanging the two inner summation variables)
  give `T₁ = 2S_A − 2S_B`;
* the same Bianchi identity gives `S_A = T₃ − W` pointwise, and a cyclic reindexing combined
  with antisymmetry gives `W = −S_C = −S_B`.

Hence `T₁ = 2(T₃ + S_B) − 2S_B = 2T₃`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary reindexings of multiple sums -/

/-- A double sum is unchanged by exchanging the two summation variables. -/
private lemma sum2_swap {m : ℕ} (f : Fin m → Fin m → ℝ) :
    (∑ a, ∑ b, f a b) = ∑ a, ∑ b, f b a :=
  Finset.sum_comm

/-- Pointwise congruence for a triple sum. -/
private lemma sum3_congr {m : ℕ} {f g : Fin m → Fin m → Fin m → ℝ}
    (h : ∀ a b c, f a b c = g a b c) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ b, ∑ c, g a b c :=
  Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => h a b c

/-- A triple sum is unchanged by the cyclic permutation `(a,b,c) ↦ (c,a,b)` of the summation
variables. -/
private lemma sum3_rot {m : ℕ} (F : Fin m → Fin m → Fin m → ℝ) :
    (∑ a, ∑ b, ∑ c, F c a b) = ∑ a, ∑ b, ∑ c, F a b c := by
  have h1 : (∑ a, ∑ b, ∑ c, F c a b) = ∑ a, ∑ c, ∑ b, F c a b :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have h2 : (∑ a, ∑ c, ∑ b, F c a b) = ∑ c, ∑ a, ∑ b, F c a b := Finset.sum_comm
  rw [h1, h2]

/-- The block exchange `∑_{a,b,c} = ∑_{c,a,b}` of a triple sum. -/
private lemma sum3_block {m : ℕ} (F : Fin m → Fin m → Fin m → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := by
  have h1 : (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have h2 : (∑ a, ∑ c, ∑ b, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm
  rw [h1, h2]

/-- Splitting a triple sum of a sum. -/
private lemma sum3_add {m : ℕ} (f g : Fin m → Fin m → Fin m → ℝ) :
    (∑ a, ∑ b, ∑ c, (f a b c + g a b c))
      = (∑ a, ∑ b, ∑ c, f a b c) + (∑ a, ∑ b, ∑ c, g a b c) := by
  simp only [Finset.sum_add_distrib]

/-- Splitting a triple sum of a difference. -/
private lemma sum3_sub {m : ℕ} (f g : Fin m → Fin m → Fin m → ℝ) :
    (∑ a, ∑ b, ∑ c, (f a b c - g a b c))
      = (∑ a, ∑ b, ∑ c, f a b c) - (∑ a, ∑ b, ∑ c, g a b c) := by
  simp only [Finset.sum_sub_distrib]

/-- Splitting a triple sum of a sum of two terms and a difference. -/
private lemma sum3_split {m : ℕ} (f g h : Fin m → Fin m → Fin m → ℝ) :
    (∑ a, ∑ b, ∑ c, (f a b c + g a b c - h a b c))
      = (∑ a, ∑ b, ∑ c, f a b c) + (∑ a, ∑ b, ∑ c, g a b c)
        - (∑ a, ∑ b, ∑ c, h a b c) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Splitting a triple sum of an alternating sum of four terms. -/
private lemma sum3_split4 {m : ℕ} (f g h k : Fin m → Fin m → Fin m → ℝ) :
    (∑ a, ∑ b, ∑ c, (f a b c - g a b c - h a b c + k a b c))
      = (∑ a, ∑ b, ∑ c, f a b c) - (∑ a, ∑ b, ∑ c, g a b c)
        - (∑ a, ∑ b, ∑ c, h a b c) + (∑ a, ∑ b, ∑ c, k a b c) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Pulling a constant out of a triple sum. -/
private lemma sum3_mul {m : ℕ} (c : ℝ) (f : Fin m → Fin m → Fin m → ℝ) :
    (∑ a, ∑ b, ∑ d, c * f a b d) = c * (∑ a, ∑ b, ∑ d, f a b d) := by
  simp only [Finset.mul_sum]

/-- Pulling a constant factor out of the first factor of a triple sum of products. -/
private lemma sum3_mul_assoc {m : ℕ} (c : ℝ) (f g : Fin m → Fin m → Fin m → ℝ) :
    (∑ a, ∑ b, ∑ d, (c * f a b d) * g a b d)
      = c * (∑ a, ∑ b, ∑ d, f a b d * g a b d) := by
  rw [show (∑ a, ∑ b, ∑ d, (c * f a b d) * g a b d)
      = ∑ a, ∑ b, ∑ d, c * (f a b d * g a b d) from
    sum3_congr fun a b d => by ring]
  exact sum3_mul c fun a b d => f a b d * g a b d

/-- Pushing a negation into a triple sum. -/
private lemma sum3_neg {m : ℕ} (f : Fin m → Fin m → Fin m → ℝ) :
    -(∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ b, ∑ c, - f a b c := by
  simp only [Finset.sum_neg_distrib]

/-! ## The main identity -/

theorem ric_Q (n : ℕ) {R : Submission.Diff.Alg.Curv4 n} (hR : Submission.Diff.Alg.IsAlgCurv R) (i j : Fin n) :
    Work.Diff.Alg.Pinch.ric (Submission.Diff.Alg.Q R) i j
      = 2 * ∑ p, ∑ q, Work.Diff.Alg.Pinch.ric R p q * R i p j q := by
  obtain ⟨hanti, hpair, hbian⟩ := hR
  -- the first Bianchi identity in antisymmetrised form
  have hpt : ∀ a b c d : Fin n, R a b c d = R a c b d - R a d b c := by
    intro a b c d
    have h1 := hbian a b c d
    have h2 : R b c a d = R a d b c := hpair a d b c
    have h3 : R c a b d = - R a c b d := hanti a c b d
    linarith
  -- antisymmetry in the last pair
  have hanti2 : ∀ a b c d : Fin n, R a b c d = - R a b d c := by
    intro a b c d
    have h1 : R a b c d = R c d a b := (hpair a b c d).symm
    have h2 : R a b d c = R d c a b := (hpair a b d c).symm
    have h3 : R d c a b = - R c d a b := hanti c d a b
    linarith
  -- the four pointwise rewrites used below
  have hA : ∀ a b c : Fin n, R a i b c = R a b i c - R a c i b := fun a b c => hpt a i b c
  have hB : ∀ a b c : Fin n, R a j b c = R a b j c - R a c j b := fun a b c => hpt a j b c
  have hC : ∀ a b c : Fin n, R a b i c = R i b a c - R i a b c := by
    intro a b c
    have h1 := hpt i b a c
    have h2 : R i c b a = - R a b i c := by
      have h2a : R i c a b = - R i c b a := hanti2 i c a b
      have h2b : R a b i c = R i c a b := hpair i c a b
      linarith
    linarith
  have hD : ∀ a b c : Fin n, R a c i b = R i b a c := fun a b c => (hpair a c i b).symm
  have hE : ∀ a b c : Fin n, R i a b c = R b c i a := fun a b c => (hpair i a b c).symm
  -- the auxiliary sums
  set T1 : ℝ := ∑ a, ∑ b, ∑ c, R a i b c * R a j b c with hT1def
  set T2 : ℝ := ∑ a, ∑ b, ∑ c, R a b a c * R i b j c with hT2def
  set T3 : ℝ := ∑ a, ∑ b, ∑ c, R a b j c * R i b a c with hT3def
  set SA : ℝ := ∑ a, ∑ b, ∑ c, R a b i c * R a b j c with hSAdef
  set SB : ℝ := ∑ a, ∑ b, ∑ c, R a c i b * R a b j c with hSBdef
  set SC : ℝ := ∑ a, ∑ b, ∑ c, R a b i c * R a c j b with hSCdef
  set SD : ℝ := ∑ a, ∑ b, ∑ c, R a c i b * R a c j b with hSDdef
  set W1 : ℝ := ∑ a, ∑ b, ∑ c, R a b j c * R i a b c with hW1def
  -- `T₁ = S_A - S_C - S_B + S_D`
  have hT1_eq : T1 = SA - SC - SB + SD := by
    rw [hT1def, hSAdef, hSCdef, hSBdef, hSDdef]
    rw [show (∑ a, ∑ b, ∑ c, R a i b c * R a j b c)
        = ∑ a, ∑ b, ∑ c, (R a b i c - R a c i b) * (R a b j c - R a c j b) from
      sum3_congr fun a b c => by rw [hA a b c, hB a b c]]
    rw [show (∑ a, ∑ b, ∑ c, (R a b i c - R a c i b) * (R a b j c - R a c j b))
        = ∑ a, ∑ b, ∑ c, (R a b i c * R a b j c - R a c i b * R a b j c
            - R a b i c * R a c j b + R a c i b * R a c j b) from
      sum3_congr fun a b c => by ring]
    rw [sum3_split4]
    ring
  -- `S_C = S_B` and `S_D = S_A`
  have hSC_SB : SC = SB := by
    rw [hSCdef, hSBdef]
    exact Finset.sum_congr rfl fun a _ => sum2_swap fun b c => R a b i c * R a c j b
  have hSD_SA : SD = SA := by
    rw [hSDdef, hSAdef]
    exact Finset.sum_congr rfl fun a _ => sum2_swap fun b c => R a c i b * R a c j b
  -- `W = -S_C`
  have hW1_eq : W1 = -SC := by
    rw [hW1def, hSCdef]
    rw [show (∑ a, ∑ b, ∑ c, R a b j c * R i a b c)
        = ∑ a, ∑ b, ∑ c, R a b j c * R b c i a from
      sum3_congr fun a b c => by rw [hE a b c]]
    rw [← sum3_rot fun a b c => R a b j c * R b c i a]
    rw [show (∑ a, ∑ b, ∑ c, R c a j b * R a b i c)
        = ∑ a, ∑ b, ∑ c, -(R a b i c * R a c j b) from
      sum3_congr fun a b c => by rw [hanti a c j b]; ring]
    rw [sum3_neg]
  -- `S_A = T₃ - W`
  have hSA_T3 : SA = T3 - W1 := by
    rw [hSAdef, hT3def, hW1def]
    rw [show (∑ a, ∑ b, ∑ c, R a b i c * R a b j c)
        = ∑ a, ∑ b, ∑ c, (R i b a c - R i a b c) * R a b j c from
      sum3_congr fun a b c => by rw [hC a b c]]
    rw [show (∑ a, ∑ b, ∑ c, (R i b a c - R i a b c) * R a b j c)
        = ∑ a, ∑ b, ∑ c, (R a b j c * R i b a c - R a b j c * R i a b c) from
      sum3_congr fun a b c => by ring]
    rw [sum3_sub]
  -- hence `T₁ = 2 T₃`
  have hSA2 : SA = T3 + SB := by
    rw [hSA_T3, hW1_eq, hSC_SB]
    ring
  have hT1_2T3 : T1 = 2 * T3 := by
    rw [hT1_eq, hSA2, hSC_SB, hSD_SA, hSA2]
    ring
  -- the expansion of `ric (Q R) i j`
  have hLHS : ric (Q R) i j = T1 + 2 * T2 - 2 * T3 := by
    rw [hT1def, hT2def, hT3def]
    simp only [ric, Q]
    rw [sum3_split (f := fun a b c => R a i b c * R a j b c)
        (g := fun a b c => 2 * R a b a c * R i b j c)
        (h := fun a b c => 2 * R a b j c * R i b a c)]
    rw [sum3_mul_assoc, sum3_mul_assoc]
  -- the right hand side is twice `T₂`
  have hRHS : 2 * (∑ p, ∑ q, ric R p q * R i p j q) = 2 * T2 := by
    rw [hT2def]
    congr 1
    simp only [ric]
    rw [show (∑ p, ∑ q, (∑ k, R k p k q) * R i p j q)
        = ∑ p, ∑ q, ∑ k, R k p k q * R i p j q from by
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro q _
      rw [Finset.sum_mul]]
    exact sum3_block fun a b c => R c a c b * R i a j b
  rw [hLHS, hRHS, hT1_2T3]
  ring

end Work.Diff.Alg.Pinch
