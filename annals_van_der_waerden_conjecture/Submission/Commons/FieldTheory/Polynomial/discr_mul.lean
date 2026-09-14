import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial

set_option autoImplicit false

namespace Commons.FieldTheory.Polynomial

noncomputable section

variable {F : Type*} [Field F]

lemma negOne_pow_mul_self {R : Type*} [Ring R] (a : ℕ) : (-1 : R) ^ a * (-1 : R) ^ a = 1 := by
  rw [← pow_add, ← two_mul]
  rw [pow_mul]; norm_num

lemma monic_eq_one_of_natDegree_eq_zero {p : F[X]} (hp : p.Monic) (hn : p.natDegree = 0) :
    p = 1 := by
  have hcoeff : p.coeff 0 = 1 := by
    have := hp.leadingCoeff
    rwa [leadingCoeff, hn] at this
  rw [eq_C_of_natDegree_eq_zero hn, hcoeff, C_1]

lemma discr_eq_signed_resultant (p : F[X]) (hp : p.Monic) (hn : 0 < p.natDegree) :
    p.discr = (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) *
      (p.resultant p.derivative p.natDegree (p.natDegree - 1)) := by
  have hdeg : 0 < p.degree := (natDegree_pos_iff_degree_pos).mp hn
  have hres := resultant_deriv (f := p) hdeg
  have hres' : (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) * p.discr =
      p.resultant p.derivative p.natDegree (p.natDegree - 1) := by
    simpa [hp.leadingCoeff] using hres.symm
  calc
    p.discr = (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) *
        ((-1) ^ (p.natDegree * (p.natDegree - 1) / 2) * p.discr) := by
      rw [← mul_assoc, negOne_pow_mul_self, one_mul]
    _ = (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) *
        (p.resultant p.derivative p.natDegree (p.natDegree - 1)) := by rw [hres']

lemma discr_eq_negOne_pow_prod_deriv (p : F[X]) (hp : p.Monic) (hps : p.Splits)
    (hn : 0 < p.natDegree) :
    p.discr = (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) *
      (p.roots.map (fun a => eval a p.derivative)).prod := by
  rw [discr_eq_signed_resultant p hp hn]
  congr 1
  rw [resultant_eq_prod_eval p p.derivative (p.natDegree - 1) (natDegree_derivative_le p) hps]
  simp [hp.leadingCoeff]

lemma eval_derivative_mul_of_mem_roots (f g : F[X]) {a : F} (ha : a ∈ f.roots) :
    eval a (f * g).derivative = eval a f.derivative * eval a g := by
  rw [derivative_mul, eval_add, eval_mul, eval_mul]
  have hf0 : f ≠ 0 := ne_zero_of_mem_roots ha
  have hroot : eval a f = 0 := (mem_roots hf0).mp ha
  simp [hroot]

lemma eval_derivative_mul_right_of_mem_roots (f g : F[X]) {b : F} (hb : b ∈ g.roots) :
    eval b (f * g).derivative = eval b f * eval b g.derivative := by
  rw [derivative_mul, eval_add, eval_mul, eval_mul]
  have hg0 : g ≠ 0 := ne_zero_of_mem_roots hb
  have hroot : eval b g = 0 := (mem_roots hg0).mp hb
  rw [hroot]
  ring

lemma prod_roots_eval_deriv_mul (f g : F[X]) :
    (f.roots.map (fun a => eval a (f * g).derivative)).prod =
      (f.roots.map (fun a => eval a f.derivative)).prod *
        (f.roots.map (fun a => eval a g)).prod := by
  classical
  have hmap :
      (f.roots.map (fun a => eval a (f * g).derivative)) =
        (f.roots.map (fun a => eval a f.derivative * eval a g)) := by
    refine Multiset.map_congr rfl ?_
    intro a ha
    exact eval_derivative_mul_of_mem_roots f g ha
  rw [hmap, Multiset.prod_map_mul]

lemma prod_roots_eval_deriv_mul_right (f g : F[X]) :
    (g.roots.map (fun b => eval b (f * g).derivative)).prod =
      (g.roots.map (fun b => eval b f)).prod *
        (g.roots.map (fun b => eval b g.derivative)).prod := by
  classical
  have hmap :
      (g.roots.map (fun b => eval b (f * g).derivative)) =
        (g.roots.map (fun b => eval b f * eval b g.derivative)) := by
    refine Multiset.map_congr rfl ?_
    intro b hb
    exact eval_derivative_mul_right_of_mem_roots f g hb
  rw [hmap, Multiset.prod_map_mul]

lemma prod_eval_right_eq_resultant (f g : F[X]) (hf : f.Monic) (hfs : f.Splits) :
    (f.roots.map (fun a => eval a g)).prod = Polynomial.resultant f g := by
  classical
  have h := resultant_eq_prod_eval f g g.natDegree le_rfl hfs
  simpa [hf.leadingCoeff] using h.symm

lemma resultant_comm' (f g : F[X]) :
    Polynomial.resultant g f = (-1) ^ (f.natDegree * g.natDegree) * Polynomial.resultant f g := by
  rw [resultant_comm]
  congr 1
  rw [mul_comm]

lemma e_succ_aux (n : ℕ) : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  have := Nat.triangle_succ n
  simpa [Nat.add_sub_cancel] using this

lemma e_add (n m : ℕ) : (n + m) * (n + m - 1) / 2 = n * (n - 1) / 2 + m * (m - 1) / 2 + n * m := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
      have h := e_succ_aux (n + m)
      have e1 : n + 1 + m = n + m + 1 := by omega
      have e2 : n + 1 + m - 1 = n + m := by omega
      rw [show (n + 1 + m) * (n + 1 + m - 1) / 2 = (n + m + 1) * (n + m) / 2 by
        rw [e1]; rw [show (n + m + 1) - 1 = n + m by omega]]
      rw [h, ih]
      rw [show (n + 1) * (n + 1 - 1) / 2 = (n + 1) * n / 2 by rw [Nat.add_sub_cancel]]
      rw [e_succ_aux n, Nat.succ_mul]
      omega


/-- `discr` is preserved by ring homomorphisms for monic polynomials. -/
lemma discr_map {L : Type*} [Field L] (φ : F →+* L) (p : F[X]) (hp : p.Monic) :
    Polynomial.discr (p.map φ) = φ (Polynomial.discr p) := by
  classical
  have hφi : Function.Injective φ := RingHom.injective φ
  have hnd : (p.map φ).natDegree = p.natDegree := natDegree_map_eq_of_injective hφi p
  by_cases hn0 : p.natDegree = 0
  · have hp1 : p = 1 := monic_eq_one_of_natDegree_eq_zero hp hn0
    rw [hp1]
    rw [Polynomial.map_one, ← Polynomial.C_1, ← Polynomial.C_1, Polynomial.discr_C, Polynomial.discr_C]
    simp
  · have hn : 0 < p.natDegree := Nat.pos_of_ne_zero hn0
    have hn' : 0 < (p.map φ).natDegree := by rwa [hnd]
    rw [discr_eq_signed_resultant (p.map φ) (hp.map φ) hn']
    rw [discr_eq_signed_resultant p hp hn]
    rw [map_mul]
    congr 1
    rw [map_pow, map_neg, map_one]
    rw [hnd]
    rw [Polynomial.derivative_map, resultant_map_map]
    simp [hnd]

/-- Main multiplicative identity when f and g split. -/
lemma discr_mul_of_splits (f g : F[X]) (hf : f.Monic) (hg : g.Monic)
    (hfs : f.Splits) (hgs : g.Splits) :
    Polynomial.discr (f * g) = Polynomial.discr f * Polynomial.discr g *
      (Polynomial.resultant f g) ^ 2 := by
  classical
  have hd1 : Polynomial.discr (1 : F[X]) = 1 := by
    rw [← Polynomial.C_1]
    exact Polynomial.discr_C (1 : F)
  by_cases hfn : f.natDegree = 0
  · have hf1 : f = 1 := monic_eq_one_of_natDegree_eq_zero hf hfn
    have hres : Polynomial.resultant (1 : F[X]) g = 1 := by
      simpa using (resultant_one_left (R := F) (g := g) (m := 0) (n := g.natDegree))
    rw [hf1, one_mul, hd1, hres]
    ring
  by_cases hgn : g.natDegree = 0
  · have hg1 : g = 1 := monic_eq_one_of_natDegree_eq_zero hg hgn
    have hres : Polynomial.resultant f (1 : F[X]) = 1 := by
      simpa using (resultant_one_right (R := F) (f := f) (m := f.natDegree) (n := 0))
    rw [hg1, mul_one, hd1, hres]
    ring
  have hfnpos : 0 < f.natDegree := Nat.pos_of_ne_zero hfn
  have hgnpos : 0 < g.natDegree := Nat.pos_of_ne_zero hgn
  have hfgmon : (f * g).Monic := hf.mul hg
  have hfgspl : (f * g).Splits := hfs.mul hgs
  have hfgdeg : (f * g).natDegree = f.natDegree + g.natDegree := hf.natDegree_mul hg
  have hfgpos : 0 < (f * g).natDegree := by omega
  have hAfg := discr_eq_negOne_pow_prod_deriv (f * g) hfgmon hfgspl hfgpos
  have hAf := discr_eq_negOne_pow_prod_deriv f hf hfs hfnpos
  have hAg := discr_eq_negOne_pow_prod_deriv g hg hgs hgnpos
  set A : F := (f.roots.map (fun a => eval a f.derivative)).prod with hAdef
  set C : F := (f.roots.map (fun a => eval a g)).prod with hCdef
  set E : F := (g.roots.map (fun b => eval b f)).prod with hEdef
  set D : F := (g.roots.map (fun b => eval b g.derivative)).prod with hDdef
  have hR : (f * g).roots = f.roots + g.roots :=
    roots_mul (mul_ne_zero hf.ne_zero hg.ne_zero)
  have hBig : ((f * g).roots.map (fun z => eval z (f * g).derivative)).prod = A * C * (E * D) := by
    rw [hR, Multiset.map_add, Multiset.prod_add]
    rw [prod_roots_eval_deriv_mul f g, prod_roots_eval_deriv_mul_right f g]
  have hC : C = Polynomial.resultant f g := by
    rw [hCdef]; exact prod_eval_right_eq_resultant f g hf hfs
  have hE : E = Polynomial.resultant g f := by
    rw [hEdef]; exact prod_eval_right_eq_resultant g f hg hgs
  have hE' : E = (-1) ^ (f.natDegree * g.natDegree) * Polynomial.resultant f g := by
    rw [hE, resultant_comm' f g]
  have hCE : C * E = (-1) ^ (f.natDegree * g.natDegree) * (Polynomial.resultant f g) ^ 2 := by
    rw [hC, hE', pow_two]
    ring
  have hEE : (f * g).natDegree * ((f * g).natDegree - 1) / 2 =
      f.natDegree * (f.natDegree - 1) / 2 + g.natDegree * (g.natDegree - 1) / 2 +
        f.natDegree * g.natDegree := by
    rw [hfgdeg]
    exact e_add f.natDegree g.natDegree
  have hSign : (-1 : F) ^ ((f * g).natDegree * ((f * g).natDegree - 1) / 2) *
      (-1 : F) ^ (f.natDegree * g.natDegree) =
      (-1 : F) ^ (f.natDegree * (f.natDegree - 1) / 2) *
        (-1 : F) ^ (g.natDegree * (g.natDegree - 1) / 2) := by
    rw [hEE]
    rw [pow_add]
    rw [mul_assoc]
    rw [negOne_pow_mul_self (f.natDegree * g.natDegree)]
    rw [pow_add]
    simp
  calc
    Polynomial.discr (f * g)
        = (-1) ^ ((f * g).natDegree * ((f * g).natDegree - 1) / 2) * (A * C * (E * D)) := by
          rw [hAfg, hBig]
    _ = (-1) ^ ((f * g).natDegree * ((f * g).natDegree - 1) / 2) * (A * (C * E) * D) := by
          ring
    _ = (-1) ^ ((f * g).natDegree * ((f * g).natDegree - 1) / 2) *
          (A * ((-1) ^ (f.natDegree * g.natDegree) * (Polynomial.resultant f g) ^ 2) * D) := by
          rw [hCE]
    _ = ((-1) ^ ((f * g).natDegree * ((f * g).natDegree - 1) / 2) *
          (-1) ^ (f.natDegree * g.natDegree)) * (A * D * (Polynomial.resultant f g) ^ 2) := by
          ring
    _ = ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          (-1) ^ (g.natDegree * (g.natDegree - 1) / 2)) * (A * D * (Polynomial.resultant f g) ^ 2) := by
          rw [hSign]
    _ = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * A *
          ((-1) ^ (g.natDegree * (g.natDegree - 1) / 2) * D) * (Polynomial.resultant f g) ^ 2 := by
          ring
    _ = Polynomial.discr f * Polynomial.discr g * (Polynomial.resultant f g) ^ 2 := by
          rw [← hAf, ← hAg]

/-- Final theorem over a general field. -/
theorem discr_mul {F : Type*} [Field F] (f g : F[X]) (hf : f.Monic) (hg : g.Monic) :
    Polynomial.discr (f * g) =
      Polynomial.discr f * Polynomial.discr g * (Polynomial.resultant f g) ^ 2 := by
  classical
  let φ : F →+* (f * g).SplittingField := algebraMap F (f * g).SplittingField
  have hφi : Function.Injective φ := RingHom.injective φ
  have hfg_mon : (f * g).Monic := hf.mul hg
  have hf' : (f.map φ).Monic := hf.map φ
  have hg' : (g.map φ).Monic := hg.map φ
  have hs0 : ((f * g).map φ).Splits := SplittingField.splits (f * g)
  rw [Polynomial.map_mul] at hs0
  have hsp := (splits_mul (f := f.map φ) (g := g.map φ) hf'.ne_zero hg'.ne_zero).mp hs0
  have hcore := discr_mul_of_splits (f.map φ) (g.map φ) hf' hg' hsp.1 hsp.2
  have hresmap : Polynomial.resultant (f.map φ) (g.map φ) = φ (Polynomial.resultant f g) := by
    have hndf : (f.map φ).natDegree = f.natDegree := natDegree_map_eq_of_injective hφi f
    have hndg : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hφi g
    have hmm := resultant_map_map f g f.natDegree g.natDegree φ
    simpa [hndf, hndg] using hmm
  apply hφi
  calc
    φ (Polynomial.discr (f * g))
        = Polynomial.discr ((f * g).map φ) := by
          rw [discr_map φ (f * g) hfg_mon]
    _ = Polynomial.discr ((f.map φ) * (g.map φ)) := by rw [Polynomial.map_mul]
    _ = Polynomial.discr (f.map φ) * Polynomial.discr (g.map φ) *
          (Polynomial.resultant (f.map φ) (g.map φ)) ^ 2 := hcore
    _ = φ (Polynomial.discr f) * φ (Polynomial.discr g) *
          (φ (Polynomial.resultant f g)) ^ 2 := by
          rw [discr_map φ f hf, discr_map φ g hg, hresmap]
    _ = φ (Polynomial.discr f * Polynomial.discr g * (Polynomial.resultant f g) ^ 2) := by
          rw [map_mul, map_mul, map_pow]

end

end Commons.FieldTheory.Polynomial