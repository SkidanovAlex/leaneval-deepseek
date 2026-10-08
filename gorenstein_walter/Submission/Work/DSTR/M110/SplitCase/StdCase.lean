/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# DS10a, split case: `N ≤ PSL(2,q)` for `N` an odd `r`-subgroup of `C(t)`, `t` split

`splitCase_std`: for `Q` with `pslImage F ≤ Q ≤ pgammaL F` (`F = GF(p^k)`, `p` odd, `p^k ≥ 5`)
and an odd `r`-subgroup `N ≤ Q` contained in the centralizer of the standard split involution
`t : x ↦ -x` and normalised by `C_Q(t)`, one has `N ≤ pslImage F`.

The proof is the counting argument of the design: an element of `N` with non-trivial Galois part
`σ` of order `r` gives, after squaring, an element `y = t₀ · γ` with `t₀` diagonal; conjugating
`y` by the square torus `dil(Fˣ)` produces `(p^k-1)/(p^(k/r)-1)` distinct conjugates in `N`,
all in the coset `N ∩ PGL · y`, so that number is at most `|N ∩ PGL| ≤ r^(v_r(p^k-1))`;
`splitArith` says it is strictly larger.  Hence `N ≤ PGL`, and odd-order elements of `PGL`
lie in `PSL`.
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.Helpers
import Submission.Work.DSTR.M110.SplitCase.card_range_dil_conj
import Submission.Work.DSTR.M110.SplitCase.splitArith

set_option maxHeartbeats 4000000

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110

open Work.AUTL2 Work.DSTR.M110.SplitAux

/-- **Counting bound for a range.**  If `ψ : G →* H` is constant equal to `σ` on the range of
`f : ι → G`, and `y ∈ N` also satisfies `ψ y = σ`, then the range of `f` has at most
`|N ∩ ker ψ|` elements (the map `z ↦ z * y⁻¹` is an injection into `N ∩ ker ψ`). -/
theorem card_range_le {G H : Type*} [Group G] [Group H] [Finite G]
    (ψ : G →* H) (N : Subgroup G) {ι : Type*} (f : ι → G) (y : G) (hy : y ∈ N) (σ : H)
    (hfN : ∀ i, f i ∈ N) (hfσ : ∀ i, ψ (f i) = σ) (hyσ : ψ y = σ) :
    Nat.card (Set.range f) ≤ Nat.card ↥(N ⊓ ψ.ker) := by
  have hinj : Function.Injective (fun z : G => z * y⁻¹) := fun a b h => mul_right_cancel h
  have hsub : (fun z : G => z * y⁻¹) '' (Set.range f) ⊆ ((N ⊓ ψ.ker : Subgroup G) : Set G) := by
    rintro w ⟨z, ⟨i, rfl⟩, rfl⟩
    refine ⟨N.mul_mem (hfN i) (N.inv_mem hy), ?_⟩
    show ψ (f i * y⁻¹) = 1
    rw [map_mul, map_inv, hfσ i, hyσ, mul_inv_cancel]
  calc Nat.card (Set.range f) = Nat.card ↥((fun z : G => z * y⁻¹) '' (Set.range f)) :=
        (Nat.card_image_of_injective hinj (Set.range f)).symm
    _ ≤ Nat.card ↥((N ⊓ ψ.ker : Subgroup G) : Set G) := by
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        exact Set.ncard_mono hsub

/-- **DS10a, split case (standard involution).** -/
theorem splitCase_std (p k r : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (hrp : r.Prime) (hro : Odd r)
    (Q : Subgroup (Equiv.Perm (P1 (GaloisField p k))))
    (hL : pslImage (GaloisField p k) ≤ Q)
    (hQ : Q ≤ pgammaL (GaloisField p k))
    (N : Subgroup (Equiv.Perm (P1 (GaloisField p k))))
    (hNle : N ≤ Q)
    (hNcent : N ≤ Subgroup.centralizer ({negPerm (GaloisField p k)} : Set _))
    (hNnorm : ∀ c : Equiv.Perm (P1 (GaloisField p k)),
        c ∈ Subgroup.centralizer ({negPerm (GaloisField p k)} : Set _) → c ∈ Q →
        ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (hNr : IsPGroup r N) :
    N ≤ pslImage (GaloisField p k) := by
  haveI : CharP (GaloisField p k) p := inferInstance
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  haveI : Fact r.Prime := ⟨hrp⟩
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  have h2 : (2 : GaloisField p k) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp hz
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hgt : 1 < p := (Fact.out : p.Prime).one_lt
    obtain ⟨m, hm⟩ := hp
    omega
  -- it suffices to show `N ≤ PGL`
  have hkey : N ≤ pglImage (GaloisField p k) := by
    by_contra hcon
    rw [SetLike.le_def] at hcon
    push_neg at hcon
    obtain ⟨x₀, hx₀N, hx₀np⟩ := hcon
    have hx₀pg : x₀ ∈ pgammaL (GaloisField p k) := hQ (hNle hx₀N)
    set x : ↥(pgammaL (GaloisField p k)) := ⟨x₀, hx₀pg⟩ with hxdef
    have hxval : (x : Equiv.Perm (P1 (GaloisField p k))) = x₀ := rfl
    have hcomm : x₀ * negPerm (GaloisField p k) = negPerm (GaloisField p k) * x₀ :=
      (Subgroup.mem_centralizer_iff.mp (hNcent hx₀N) _ (Set.mem_singleton _)).symm
    have hgal : galMap (GaloisField p k) x ≠ 1 := fun h =>
      hx₀np ((galPart_eq_one_iff (GaloisField p k) x).mp h)
    -- the order of the Galois part is a power of `r`
    obtain ⟨n0, hn0⟩ := hNr (⟨x₀, hx₀N⟩ : ↥N)
    have hxpow : x ^ (r ^ n0) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hxval]
      exact congrArg Subtype.val hn0
    have hdvd : orderOf (galMap (GaloisField p k) x) ∣ r ^ n0 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have h1 := map_pow (galMap (GaloisField p k)) x (r ^ n0)
      rw [hxpow, map_one] at h1
      exact h1.symm
    obtain ⟨s, _hsle, hseq⟩ := (Nat.dvd_prime_pow hrp).mp hdvd
    have hspos : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · exfalso
        rw [h0, pow_zero] at hseq
        exact hgal (orderOf_eq_one_iff.mp hseq)
      · exact h0
    -- `x₁ = x^(r^(s-1))`
    set x₁ : ↥(pgammaL (GaloisField p k)) := x ^ (r ^ (s - 1)) with hx1
    have hgal1 : orderOf (galMap (GaloisField p k) x₁) = r := by
      rw [hx1, map_pow]
      have hgord : orderOf (galMap (GaloisField p k) x) = r ^ s := hseq
      have hgr : (galMap (GaloisField p k) x) ^ (r ^ s) = 1 := by
        rw [← hgord]; exact pow_orderOf_eq_one _
      refine orderOf_eq_prime ?_ ?_
      · rw [← pow_mul, show r ^ (s - 1) * r = r ^ s by rw [← pow_succ]; congr 1; omega]
        exact hgr
      · intro h1
        have hdvd' : r ^ s ∣ r ^ (s - 1) := by
          rw [← hgord, orderOf_dvd_iff_pow_eq_one]; exact h1
        exact absurd ((Nat.pow_dvd_pow_iff_le_right hrp.one_lt).mp hdvd') (by omega)
    have hx₁N : (x₁ : Equiv.Perm (P1 (GaloisField p k))) ∈ N := by
      rw [hx1, Subgroup.coe_pow, hxval]
      exact N.pow_mem hx₀N _
    have hyN : ((x₁ * x₁ : ↥(pgammaL (GaloisField p k))) :
        Equiv.Perm (P1 (GaloisField p k))) ∈ N := by
      rw [Subgroup.coe_mul]
      exact N.mul_mem hx₁N hx₁N
    have hcomm₁ : (x₁ : Equiv.Perm (P1 (GaloisField p k))) * negPerm (GaloisField p k) =
        negPerm (GaloisField p k) * (x₁ : Equiv.Perm (P1 (GaloisField p k))) := by
      rw [hx1, Subgroup.coe_pow, hxval]
      exact (show Commute x₀ (negPerm (GaloisField p k)) from hcomm).pow_left _ |>.eq
    -- `y = x₁²` has diagonal `PGL`-part
    obtain ⟨t, σ, hyt⟩ := sq_decomp_torus (GaloisField p k) h2 x₁ hcomm₁
    have hyval : ((x₁ * x₁ : ↥(pgammaL (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k))) =
        (t : Equiv.Perm (P1 (GaloisField p k))) * galHom (GaloisField p k) σ := hyt
    have hygal : galMap (GaloisField p k) (x₁ * x₁) = σ := by
      have h := galPart_unique (GaloisField p k) (x₁ * x₁)
        (c := (t : Equiv.Perm (P1 (GaloisField p k))))
        (τ := galHom (GaloisField p k) σ) (torSub_le_pglImage (GaloisField p k) t.2)
        (galSub_mem_galHom (GaloisField p k) σ) (by rw [hyt])
      exact Galois.galHom_injective (GaloisField p k) h
    have hσr : orderOf σ = r := by
      have h1 : (galMap (GaloisField p k) x₁) ^ 2 = σ := by
        rw [← hygal]
        have h2' := map_mul (galMap (GaloisField p k)) x₁ x₁
        rw [← pow_two] at h2'
        exact h2'.symm
      rw [← h1]
      refine orderOf_eq_prime ?_ ?_
      · rw [← pow_mul, mul_comm 2 r, pow_mul, ← hgal1, pow_orderOf_eq_one, one_pow]
      · intro h1'
        have hdvd2 : orderOf (galMap (GaloisField p k) x₁) ∣ 2 := by
          rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact h1'
        rw [hgal1] at hdvd2
        have hle := Nat.le_of_dvd (by norm_num) hdvd2
        have hreq : r = 2 := le_antisymm hle hrp.two_le
        rw [hreq] at hro
        norm_num at hro
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp t.2
    have hyval' : ((x₁ * x₁ : ↥(pgammaL (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k))) =
        (smulHom (GaloisField p k) a) * galHom (GaloisField p k) σ := by
      rw [hyval, ← ha]
    -- the conjugating family
    set Φ : (GaloisField p k)ˣ → Equiv.Perm (P1 (GaloisField p k)) :=
      fun u => dil (GaloisField p k) u *
        ((x₁ * x₁ : ↥(pgammaL (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k))) *
        (dil (GaloisField p k) u)⁻¹ with hΦ
    have hΦN : ∀ u, Φ u ∈ N := by
      intro u
      have hmem : dil (GaloisField p k) u ∈
          Subgroup.centralizer ({negPerm (GaloisField p k)} : Set _) ⊓ Q := by
        refine ⟨?_, hL (dil_mem (GaloisField p k) u)⟩
        refine (Subgroup.mem_centralizer_iff).mpr ?_
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (dil_comm_negPerm (GaloisField p k) u).symm
      have := hNnorm (dil (GaloisField p k) u) hmem.1 hmem.2
        (((x₁ * x₁ : ↥(pgammaL (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k)))) hyN
      simpa only [hΦ] using this
    have hΦpg : ∀ u, Φ u ∈ pgammaL (GaloisField p k) := fun u => hQ (hNle (hΦN u))
    have hΦσ : ∀ u, galMap (GaloisField p k) ⟨Φ u, hΦpg u⟩ = σ := by
      intro u
      have hdlpg : dil (GaloisField p k) u ∈ pgammaL (GaloisField p k) :=
        ((pslImage_le_pglImage (GaloisField p k)).trans le_sup_left)
          (dil_mem (GaloisField p k) u)
      have hc : ((⟨dil (GaloisField p k) u, hdlpg⟩ : ↥(pgammaL (GaloisField p k))) :
          Equiv.Perm (P1 (GaloisField p k))) ∈ pglImage (GaloisField p k) :=
        pslImage_le_pglImage (GaloisField p k) (dil_mem (GaloisField p k) u)
      have hconj := galMap_conj_mem_pglImage (GaloisField p k) _ hc (x₁ * x₁)
      have hΦeq : (⟨Φ u, hΦpg u⟩ : ↥(pgammaL (GaloisField p k))) =
          (⟨dil (GaloisField p k) u, hdlpg⟩ : ↥(pgammaL (GaloisField p k))) * (x₁ * x₁) *
            (⟨dil (GaloisField p k) u, hdlpg⟩ : ↥(pgammaL (GaloisField p k)))⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hΦ]
      rw [hΦeq, hconj, hygal]
    -- counting
    have hcount := Work.DSTR.M110.SplitCase.card_range_dil_conj p k r hp (by omega : 1 ≤ k) hrp hro σ hσr a
    have hcount' : Nat.card (Set.range Φ) = (p ^ k - 1) / (p ^ (k / r) - 1) := by
      have hset : Set.range Φ = Set.range (fun u : (GaloisField p k)ˣ =>
          dil (GaloisField p k) u *
            (smulHom (GaloisField p k) a * galHom (GaloisField p k) σ) *
            (dil (GaloisField p k) u)⁻¹) := by
        ext w
        constructor
        · rintro ⟨u, rfl⟩
          exact ⟨u, by rw [hΦ, hyval']⟩
        · rintro ⟨u, rfl⟩
          exact ⟨u, by rw [hΦ, hyval']⟩
      rw [hset]
      exact hcount
    -- upper bound by `|N ∩ PGL|`
    have hrk : r ∣ k := Work.DSTR.M110.SplitCase.dvd_of_orderOf_eq p k r hk hrp σ hσr
    have hub : Nat.card (Set.range Φ) ≤ r ^ ((p ^ k - 1).factorization r) := by
      have hKtors : N ⊓ pglImage (GaloisField p k) ≤ torSub (GaloisField p k) := by
        intro z hz
        obtain ⟨hzN, hzpgl⟩ := hz
        have hzcomm : z * negPerm (GaloisField p k) = negPerm (GaloisField p k) * z :=
          (Subgroup.mem_centralizer_iff.mp (hNcent hzN) _ (Set.mem_singleton _)).symm
        have hzodd : Odd (orderOf z) := by
          obtain ⟨n, hn⟩ := hNr (⟨z, hzN⟩ : ↥N)
          have hdvd : orderOf z ∣ r ^ n := by
            rw [orderOf_dvd_iff_pow_eq_one]
            simpa using congrArg Subtype.val hn
          by_contra hcontra
          rw [Nat.not_odd_iff_even] at hcontra
          exact hro.pow.not_two_dvd_nat ((even_iff_two_dvd.mp hcontra).trans hdvd)
        exact mem_torSub_of_odd_order (GaloisField p k) h2 hzpgl hzcomm hzodd
      have hFcard : Fintype.card (GaloisField p k) = p ^ k := by
        rw [← Nat.card_eq_fintype_card, GaloisField.card p k hk]
      have hKcard : Nat.card ↥(N ⊓ pglImage (GaloisField p k)) ∣ p ^ k - 1 := by
        have h1 := Subgroup.card_dvd_of_le hKtors
        rw [card_torSub, hFcard] at h1
        exact h1
      have hKr : IsPGroup r ↥(N ⊓ pglImage (GaloisField p k)) :=
        hNr.of_injective (Subgroup.inclusion inf_le_left) (fun a b hab => by
          apply Subtype.ext
          exact congrArg (fun z : ↥N => (z : Equiv.Perm (P1 (GaloisField p k)))) hab)
      have hne : p ^ k - 1 ≠ 0 := by
        have h2p : 2 ≤ p ^ k := by
          calc 2 ≤ p ^ 1 := by simpa using (Fact.out : p.Prime).two_le
            _ ≤ p ^ k := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (Nat.pos_of_ne_zero hk)
        omega
      have h2' : Nat.card ↥(N ⊓ pglImage (GaloisField p k)) ≤
          r ^ ((p ^ k - 1).factorization r) := by
        obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hKr
        rw [hm]
        refine Nat.pow_le_pow_right hrp.pos ?_
        exact (Nat.Prime.pow_dvd_iff_le_factorization hrp hne).mp (by rw [← hm]; exact hKcard)
      have h1 : Nat.card (Set.range Φ) ≤ Nat.card ↥(N ⊓ pglImage (GaloisField p k)) := by
        set ψ : ↥N →* (GaloisField p k ≃+* GaloisField p k) :=
          (galMap (GaloisField p k)).comp
            (Subgroup.inclusion (fun x hx => hQ (hNle hx))) with hψ
        set f : (GaloisField p k)ˣ → ↥N := fun u => ⟨Φ u, hΦN u⟩ with hf
        have hfN : ∀ u, f u ∈ (⊤ : Subgroup ↥N) := fun u => Subgroup.mem_top _
        have hfσ : ∀ u, ψ (f u) = σ := by
          intro u
          show galMap (GaloisField p k) (⟨Φ u, hΦpg u⟩ : ↥(pgammaL (GaloisField p k))) = σ
          exact hΦσ u
        have hyσ : ψ ⟨_, hyN⟩ = σ := by
          show galMap (GaloisField p k)
            (⟨_, _⟩ : ↥(pgammaL (GaloisField p k))) = σ
          exact hygal
        have hmain := card_range_le ψ ⊤ f ⟨_, hyN⟩ (Subgroup.mem_top _) σ hfN hfσ hyσ
        rw [top_inf_eq] at hmain
        have hcardS : Nat.card (Set.range f) = Nat.card (Set.range Φ) := by
          have hset : Subtype.val '' (Set.range f) = Set.range Φ := by
            ext w
            constructor
            · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
              exact ⟨u, rfl⟩
            · rintro ⟨u, rfl⟩
              exact ⟨f u, ⟨u, rfl⟩, rfl⟩
          rw [← Nat.card_image_of_injective (f := Subtype.val) Subtype.val_injective
            (Set.range f), hset]
        have hcardker : Nat.card ↥ψ.ker =
            Nat.card ↥(N ⊓ pglImage (GaloisField p k)) := by
          apply Nat.card_congr
          refine
            { toFun := fun z => ⟨(z.1 : ↥N).1, ⟨(z.1 : ↥N).2, ?_⟩⟩
              invFun := fun w => ⟨⟨w.1, w.2.1⟩, ?_⟩
              left_inv := fun z => Subtype.ext (Subtype.ext rfl)
              right_inv := fun w => Subtype.ext rfl }
          · exact (galPart_eq_one_iff (GaloisField p k) _).mp (MonoidHom.mem_ker.mp z.2)
          · exact MonoidHom.mem_ker.mpr ((galPart_eq_one_iff (GaloisField p k)
              ⟨w.1, hQ (hNle w.2.1)⟩).mpr w.2.2)
        rwa [hcardS, hcardker] at hmain
      exact le_trans h1 h2'
    have harith : r ^ ((p ^ k - 1).factorization r) < (p ^ k - 1) / (p ^ (k / r) - 1) := by
      have h1 : 1 ≤ k / r :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hrk) hrp.pos
      have h2'' := Work.DSTR.M110.SplitCase.splitArith p r (k / r) (Fact.out : p.Prime) hp hrp hro h1
      rwa [Nat.mul_div_cancel' hrk] at h2''
    omega
  intro x hx
  have hord : Odd (orderOf x) := by
    obtain ⟨n, hn⟩ := hNr (⟨x, hx⟩ : ↥N)
    have hdvd : orderOf x ∣ r ^ n := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa using congrArg Subtype.val hn
    by_contra hcontra
    rw [Nat.not_odd_iff_even] at hcontra
    exact hro.pow.not_two_dvd_nat ((even_iff_two_dvd.mp hcontra).trans hdvd)
  exact oddPglImageMemPslImage p k x (hkey hx) hord

end Work.DSTR.M110
