import Mathlib
import Submission.Work.DSTR.M110.PiCoreFacts
import Submission.Work.DSTR.M110.SylowGen
import Submission.Work.DSTR.M110.Aut.pglIndex
import Submission.Work.DSTR.M110.Galois.decomposition
import Submission.Work.DSTR.M110.arithOrbitSubOne
import Submission.Work.DSTR.M110.arithOrbitAddOne
import Submission.Work.DSTR.M110.nonsplitAux
import Submission.Work.DSTR.M110.theTorusFacts
import Submission.Work.DSTR.M110.torusConjPow
import Submission.Work.DSTR.M110.oddCentralizerLeTorus
import Submission.Work.DSTR.M110.arithAddOneOddAux
import Submission.Work.DSTR.M110.frobeniusRingAut
import Submission.Work.DSTR.M110.cardFixedZpowers
import Submission.Work.DSTR.M110.cardFixedZpowersZpow
import Submission.Work.DSTR.M110.zpowersOddOrder
import Submission.Work.DSTR.M110.orbitCardZpowers

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Polynomial

namespace Work.DSTR.M110

/-- `pglImage F` is normal in `pgammaL F`. -/
private lemma conj_mem_pglImage_aux {F : Type*} [Field F] [DecidableEq F]
    {g : Equiv.Perm (Work.AUTL2.P1 F)} (hg : g ∈ Work.AUTL2.pgammaL F)
    {y : Equiv.Perm (Work.AUTL2.P1 F)} (hy : y ∈ Work.AUTL2.pglImage F) :
    g * y * g⁻¹ ∈ Work.AUTL2.pglImage F := by
  have hnorm : Work.AUTL2.pgammaL F ≤
      Subgroup.normalizer (Work.AUTL2.pglImage F : Set (Equiv.Perm (Work.AUTL2.P1 F))) := by
    rw [Work.AUTL2.pgammaL]
    exact sup_le Subgroup.le_normalizer (Work.AUTL2.Galois.galSub_le_normalizer_pglImage F)
  exact (Subgroup.le_normalizer_iff.mp hnorm) g hg y hy

/-- Every element of an `r`-group with `r` odd has odd order. -/
private lemma odd_orderOf_of_mem_isPGroup' {G : Type*} [Group G] (r : ℕ) (hr : Odd r)
    (N : Subgroup G) (hNr : IsPGroup r N) {x : G} (hx : x ∈ N) : Odd (orderOf x) := by
  obtain ⟨n, hn⟩ := hNr ⟨x, hx⟩
  have h1 : orderOf (⟨x, hx⟩ : ↥N) ∣ r ^ n := orderOf_dvd_iff_pow_eq_one.mpr hn
  rw [Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat (hr.pow) h1

/-- **The non-split case of DS10a.**  Let `F = GF(p^k)` with `p` an odd prime and `p^k ≥ 5`,
let `t ∈ PGL(2,F) ≤ Sym(ℙ¹(F))` be a fixed-point-free involution and let `N ≤ Q` be an
`r`-group (`r` an odd prime) contained in `C(t)` and normalized by `C_Q(t)`.  Then
`N ≤ PSL(2,F)`.

The proof follows Bender's argument: an element `x ∈ N \ PSL`, viewed in
`PΓL = PGL ⋊ Gal`, has non-trivial Galois part `φ`, and a suitable power `x'` of `x` has
Galois part of order `r = k/gcd(i,k)` (a Frobenius power `a ↦ a^(p^i)`).  The odd part `T_odd`
(cyclic of odd order `m`) of the non-split torus `T = C_{PGL}(t)` acts on `x'` by the
`±p^i`-power map, so the `T_odd`-orbit of `x'` has `m / gcd(m, p^i ∓ 1)` elements.  On the
other hand this orbit lies in the `x'`-coset of `N ∩ PGL ⊆ T_odd ∩ N`, an `r`-group, so it has
at most `r^(v_r m)` elements; the two estimates contradict `arithAddOneOddAux`. -/
theorem nonsplitCase (p k r : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (hrp : r.Prime) (hro : Odd r)
    (Q : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hL : Work.AUTL2.pslImage (GaloisField p k) ≤ Q)
    (hQ : Q ≤ Work.AUTL2.pgammaL (GaloisField p k))
    (t : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (htQ : t ∈ Q) (ht2 : orderOf t = 2) (htpgl : t ∈ Work.AUTL2.pglImage (GaloisField p k))
    (htfpf : ∀ x : Work.AUTL2.P1 (GaloisField p k), t x ≠ x)
    (N : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hNle : N ≤ Q)
    (hNcent : N ≤ Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))))
    (hNnorm : ∀ c : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)),
        c ∈ Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) → c ∈ Q →
        ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (hNr : IsPGroup r N) :
    N ≤ Work.AUTL2.pslImage (GaloisField p k) := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  haveI : Finite (GaloisField p k ≃+* GaloisField p k) :=
    Finite.of_injective (fun e : GaloisField p k ≃+* GaloisField p k =>
        (e : GaloisField p k → GaloisField p k))
      (fun a b h => RingEquiv.ext (fun x => congrFun h x))
  obtain ⟨B, c, htB, hB, hBns⟩ := exists_mat_of_mem_pglImage t htpgl ht2
  have hc : ¬ IsSquare c :=
    not_isSquare_of_fixedPointFree B c hB (by rw [← htB]; exact htfpf)
  obtain ⟨hcyc, hcard, hcent⟩ := theTorusFacts p k hp hk B c hB hc
  have hcentT : theTorus B c hB ≤
      Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) := by
    have h := hcent
    rwa [← htB] at h
  haveI : Fact (Irreducible (X ^ 2 - C c : (GaloisField p k)[X])) :=
    ⟨irreducible_X_sq_sub_C hc⟩
  -- an element of `N` outside `pslImage` would have non-trivial Galois part
  intro y hy
  by_contra hynot
  have hyQ : y ∈ Q := hNle hy
  set x : ↥(Work.AUTL2.pgammaL (GaloisField p k)) := ⟨y, hQ hyQ⟩ with hxdef
  have hxcoe : (x : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) = y := rfl
  have hgal : Work.DSTR.M110.SplitAux.galMap (GaloisField p k) x ≠ 1 := by
    intro h1
    have hypgl : y ∈ Work.AUTL2.pglImage (GaloisField p k) := by
      have h2 := (Work.DSTR.M110.SplitAux.galPart_eq_one_iff (GaloisField p k) x).mp h1
      rwa [hxcoe] at h2
    exact hynot (oddPglImageMemPslImage' p k y hypgl
      (odd_orderOf_of_mem_isPGroup' r hro N hNr hy))
  -- The Galois part of `x` is Frob^i for some `i`
  set φ : GaloisField p k ≃+* GaloisField p k :=
    Work.DSTR.M110.SplitAux.galMap (GaloisField p k) x with hφdef
  have hφne : φ ≠ 1 := hgal
  obtain ⟨a, ha⟩ := hNr ⟨y, hy⟩
  have hya : orderOf y ∣ r ^ a := by
    have hy1 : y ^ r ^ a = 1 := by
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
        congrArg (fun w : ↥N => (w : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) ha
    exact orderOf_dvd_iff_pow_eq_one.mpr hy1
  have hsdvd : orderOf φ ∣ r ^ a := by
    rw [hφdef]
    have h1 : orderOf (Work.DSTR.M110.SplitAux.galMap (GaloisField p k) x) ∣ orderOf x :=
      orderOf_map_dvd (Work.DSTR.M110.SplitAux.galMap (GaloisField p k)) x
    have h2 : orderOf x = orderOf y := by rw [← Subgroup.orderOf_coe x, hxcoe]
    rw [h2] at h1
    exact h1.trans hya
  -- `orderOf φ = r ^ b` with `b ≥ 1`
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hrp).mp hsdvd
  have hbpos : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · exfalso
      rw [h, pow_zero] at hb
      exact hφne (orderOf_eq_one_iff.mp hb)
    · exact h
  set y' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) := y ^ r ^ (b - 1) with hy'def
  have hy'N : y' ∈ N := N.pow_mem hy _
  have hy'Q : y' ∈ Q := hNle hy'N
  have hy'pg : y' ∈ Work.AUTL2.pgammaL (GaloisField p k) := hQ hy'Q
  have hφ' : Work.DSTR.M110.SplitAux.galMap (GaloisField p k) ⟨y', hy'pg⟩ = φ ^ r ^ (b - 1) := by
    have hx'' : (⟨y', hy'pg⟩ : ↥(Work.AUTL2.pgammaL (GaloisField p k))) = x ^ r ^ (b - 1) := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, hxcoe, hy'def]
    rw [hx'', map_pow, ← hφdef]
  have hordφ' : orderOf (φ ^ r ^ (b - 1)) = r := by
    have h1 : orderOf (φ ^ r ^ (b - 1)) = orderOf φ / (orderOf φ).gcd (r ^ (b - 1)) :=
      orderOf_pow φ
    rw [hb] at h1
    have hg : (r ^ b).gcd (r ^ (b - 1)) = r ^ (b - 1) :=
      Nat.gcd_eq_right (Nat.pow_dvd_pow r (by omega))
    rw [hg] at h1
    rw [h1, Nat.pow_div (by omega : b - 1 ≤ b) hrp.pos,
      show b - (b - 1) = 1 by omega, pow_one]
  have hφ'r : orderOf (Work.DSTR.M110.SplitAux.galMap (GaloisField p k) ⟨y', hy'pg⟩) = r := by
    rw [hφ']; exact hordφ'
  -- write the Galois part of `y'` as a Frobenius power
  obtain ⟨i, hik, hi_pow, hi_ord⟩ :=
    frobeniusRingAut p k (Nat.pos_of_ne_zero hk)
      (Work.DSTR.M110.SplitAux.galMap (GaloisField p k) ⟨y', hy'pg⟩)
  have hrk : k / i.gcd k = r := hi_ord.symm.trans hφ'r
  -- element of the group
  set x' : ↥(Work.AUTL2.pgammaL (GaloisField p k)) := ⟨y', hy'pg⟩ with hx'def
  have hx'coe : (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) = y' := rfl
  have hx'N : (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) ∈ N := by
    rw [hx'coe]; exact hy'N
  have hi' : ∀ aa : GaloisField p k,
      Work.DSTR.M110.SplitAux.galMap (GaloisField p k) x' aa = aa ^ (p ^ i) := hi_pow
  -- `x'` centralizes `t = pglHom (mk B)`
  have hx'cent : (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) *
      Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B) =
      Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B) *
        (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) := by
    have hycent : y * t = t * y :=
      ((Subgroup.mem_centralizer_iff.mp (hNcent hy)) t rfl).symm
    have hy'cent : Commute y t := hycent
    have hy''cent : y' * t = t * y' := by
      rw [hy'def]
      exact hy'cent.pow_left _
    calc (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) *
          Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B)
        = y' * t := by rw [hx'coe, ← htB]
      _ = t * y' := hy''cent
      _ = Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B) *
            (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) := by rw [htB, hx'coe]
  -- `i ≥ 1`
  have hi1 : 1 ≤ i := by
    by_contra hcon
    have hi0 : i = 0 := by omega
    rw [hi0, Nat.gcd_zero_left] at hrk
    have h1 : r = 1 := by rw [← hrk]; exact Nat.div_self (Nat.pos_of_ne_zero hk)
    exact hrp.ne_one h1
  -- ===== the odd part of the non-split torus =====
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(theTorus B c hB))
  set ζ : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) :=
    (g : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) with hζdef
  have hζmem : ζ ∈ theTorus B c hB := by rw [hζdef]; exact g.2
  have hζgen : Subgroup.zpowers ζ = theTorus B c hB := by
    apply le_antisymm
    · rw [Subgroup.zpowers_le]; exact hζmem
    · intro w hw
      have hw' : (⟨w, hw⟩ : ↥(theTorus B c hB)) ∈ Subgroup.zpowers g := hg ⟨w, hw⟩
      rw [Subgroup.mem_zpowers_iff] at hw' ⊢
      obtain ⟨m', hm'⟩ := hw'
      refine ⟨m', ?_⟩
      have h2 := congrArg (fun u : ↥(theTorus B c hB) =>
        (u : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) hm'
      rw [hζdef]
      simpa using h2
  have hζord : orderOf ζ = p ^ k + 1 := by
    rw [← Nat.card_zpowers ζ, hζgen, hcard]
  -- the odd part
  set v2 : ℕ := (p ^ k + 1).factorization 2 with hv2def
  set z : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) := ζ ^ 2 ^ v2 with hzdef
  have hNne : p ^ k + 1 ≠ 0 := by
    have h2 : 0 < p ^ k := pow_pos (Fact.out : p.Prime).pos k
    omega
  have h2dvd : 2 ^ ((p ^ k + 1).factorization 2) ∣ p ^ k + 1 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hNne).mpr le_rfl
  have h2v2dvd : 2 ^ v2 ∣ p ^ k + 1 := by rw [hv2def]; exact h2dvd
  set m : ℕ := (p ^ k + 1) / 2 ^ ((p ^ k + 1).factorization 2) with hmdef
  have hzm : Nat.card ↥(Subgroup.zpowers z) = m := by
    rw [Nat.card_zpowers, hzdef, orderOf_pow, hζord, Nat.gcd_eq_right h2v2dvd, hv2def, hmdef]
  have hzord : orderOf z = m := by rw [← Nat.card_zpowers z, hzm]
  have hmpos : 0 < m := by
    rw [hmdef]
    exact Nat.div_pos (Nat.le_of_dvd (by omega) h2dvd) (by positivity)
  have hmodd : Odd m := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd, hmdef]
    exact Nat.not_dvd_ordCompl Nat.prime_two hNne
  have hzT : z ∈ theTorus B c hB := by
    rw [← hζgen]
    exact Subgroup.npow_mem_zpowers ζ (2 ^ v2)
  have hzlt : Subgroup.zpowers z ≤ theTorus B c hB := Subgroup.zpowers_le.mpr hzT
  -- odd-order elements of `pglImage` are in `pslImage ⊆ Q`
  have hz_psl : ∀ w ∈ Subgroup.zpowers z, w ∈ Work.AUTL2.pslImage (GaloisField p k) := by
    intro w hw
    have hwpgl : w ∈ Work.AUTL2.pglImage (GaloisField p k) :=
      theTorus_le_pglImage B c hB (hzlt hw)
    have hdvdw : orderOf w ∣ m := by
      have h1 := orderOf_dvd_of_mem_zpowers hw
      rwa [hzord] at h1
    exact oddPglImageMemPslImage' p k w hwpgl (Odd.of_dvd_nat hmodd hdvdw)
  have hwQ : ∀ w ∈ Subgroup.zpowers z, w ∈ Q := fun w hw => hL (hz_psl w hw)
  have hwC : ∀ w ∈ Subgroup.zpowers z, w ∈
      Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) :=
    fun w hw => hcentT (hzlt hw)
  -- the action of `x'` on the torus is the `ε`-power map
  obtain ⟨ε, hεsign, hεact⟩ :=
    torusConjPow p k hk B c hB hc x' hx'cent i hi'
  have hact : ∀ w ∈ Subgroup.zpowers z,
      (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * w *
          (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))⁻¹ = w ^ ε := by
    intro w hw
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp (hzlt hw)
    rw [hεact u, ← map_zpow]
  -- ===== the orbit count =====
  set d : ℕ := m.gcd (ε - 1).natAbs with hddef
  have hstabcard : Nat.card {w : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) //
        w ∈ Subgroup.zpowers z ∧ w ^ ε = w} = d := by
    rw [hddef]
    have hiff : ∀ w : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)),
        (w ∈ Subgroup.zpowers z ∧ w ^ ε = w) ↔
          (w ∈ Subgroup.zpowers z ∧ w ^ (ε - 1) = 1) := by
      intro w
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have h3 : w ^ (ε - 1) = w ^ ε * w ^ (-1 : ℤ) := by
          rw [show ε - 1 = ε + (-1 : ℤ) by ring, zpow_add]
        rw [h3, h2, zpow_neg_one]
        simp
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have h3 : w ^ ε = w ^ (ε - 1 + 1) := by rw [show ε - 1 + 1 = ε by ring]
        rw [h3, zpow_add, h2, one_mul, zpow_one]
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    exact cardFixedZpowersZpow z hzord (ε - 1)
  have horb2 : Nat.card {y : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) //
        ∃ w ∈ Subgroup.zpowers z,
          y = w * (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * w⁻¹} * d = m := by
    have h1 := orbitCardZpowers z (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) ε hact
    rw [hzm, hstabcard] at h1
    exact h1
  have hOrb_le : Nat.card {y : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) //
        ∃ w ∈ Subgroup.zpowers z,
          y = w * (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * w⁻¹} ≤
      Nat.card ↥(N ⊓ Work.AUTL2.pglImage (GaloisField p k)) := by
    have hmem : ∀ y : {y : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) //
        ∃ w ∈ Subgroup.zpowers z,
          y = w * (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * w⁻¹},
        (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))⁻¹ * y.1 ∈
          N ⊓ Work.AUTL2.pglImage (GaloisField p k) := by
      rintro ⟨yy, w, hw, rfl⟩
      refine ⟨?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx'N)
          (hNnorm w (hwC w hw) (hwQ w hw)
            (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) hx'N)
      · have hwpgl : w ∈ Work.AUTL2.pglImage (GaloisField p k) :=
          theTorus_le_pglImage B c hB (hzlt hw)
        have hxg : (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) ∈
            Work.AUTL2.pgammaL (GaloisField p k) := x'.2
        have ha : (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))⁻¹ * w *
            (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) ∈
            Work.AUTL2.pglImage (GaloisField p k) := by
          simpa using conj_mem_pglImage_aux (Subgroup.inv_mem _ hxg) hwpgl
        have heq : (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))⁻¹ *
              (w * (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * w⁻¹) =
            ((x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))⁻¹ * w *
              (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) * w⁻¹ := by group
        rw [heq]
        exact Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hwpgl)
    exact Nat.card_le_card_of_injective
      (fun y => (⟨(x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))⁻¹ * y.1, hmem y⟩ :
        ↥(N ⊓ Work.AUTL2.pglImage (GaloisField p k))))
      (fun a b hab => Subtype.ext (mul_left_cancel (congrArg Subtype.val hab)))
  -- the cardinality of `N ⊓ pglImage` is a power of `r` dividing `m`
  haveI : Fact r.Prime := ⟨hrp⟩
  have hP : IsPGroup r ↥(N ⊓ Work.AUTL2.pglImage (GaloisField p k)) :=
    hNr.to_le inf_le_left
  obtain ⟨s, hs⟩ := hP.exists_card_eq
  have hle_sub : N ⊓ Work.AUTL2.pglImage (GaloisField p k) ≤ Subgroup.zpowers z := by
    rintro v ⟨hvN, hvpgl⟩
    have hvodd : Odd (orderOf v) := odd_orderOf_of_mem_isPGroup' r hro N hNr hvN
    have hvt : v ∈ theTorus B c hB :=
      oddCentralizerLeTorus p k hk B c hB hc hBns v hvpgl (by
        have h := hNcent hvN
        rwa [htB] at h) hvodd
    have hvζ : v ∈ Subgroup.zpowers ζ := by rw [hζgen]; exact hvt
    have h := zpowersOddOrder ζ v hvζ hvodd
    rw [hζord, ← hv2def] at h
    rwa [← hzdef] at h
  have hdvd : r ^ s ∣ m := by
    rw [← hs]
    have h1 := Subgroup.card_subgroup_dvd_card
      ((N ⊓ Work.AUTL2.pglImage (GaloisField p k)).subgroupOf (Subgroup.zpowers z))
    have h2 : Nat.card ↥((N ⊓ Work.AUTL2.pglImage (GaloisField p k)).subgroupOf
          (Subgroup.zpowers z)) = Nat.card ↥(N ⊓ Work.AUTL2.pglImage (GaloisField p k)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle_sub).toEquiv
    rw [h2, hzm] at h1
    exact h1
  have hs_le : s ≤ m.factorization r :=
    (Nat.Prime.pow_dvd_iff_le_factorization hrp hmpos.ne').mp hdvd
  have hOrb_bound : Nat.card {y : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) //
        ∃ w ∈ Subgroup.zpowers z,
          y = w * (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * w⁻¹} ≤
      r ^ m.factorization r := by
    rw [hs] at hOrb_le
    exact hOrb_le.trans (Nat.pow_le_pow_right hrp.pos hs_le)
  -- ===== the arithmetic contradiction =====
  obtain ⟨harith1, harith2⟩ := arithAddOneOddAux p k i (Fact.out) hp hi1 hik
    (by rw [hrk]; exact hrp) (by rw [hrk]; exact hro)
  rw [hrk, ← hmdef] at harith1 harith2
  have horb_eq : Nat.card {y : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) //
        ∃ w ∈ Subgroup.zpowers z,
          y = w * (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * w⁻¹} = m / d := by
    have hdpos : 0 < d := by rw [hddef]; exact Nat.gcd_pos_of_pos_left _ hmpos
    rw [show m = Nat.card {y : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) //
        ∃ w ∈ Subgroup.zpowers z,
          y = w * (x' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * w⁻¹} * d
          from horb2.symm]
    exact (Nat.mul_div_cancel _ hdpos).symm
  rw [horb_eq] at hOrb_bound
  have hnat1 : (ε - 1).natAbs = p ^ i - 1 ∨ (ε - 1).natAbs = p ^ i + 1 := by
    rcases hεsign with h | h
    · left
      rw [h]
      have hcast : ((p : ℤ) ^ i - 1) = ((p ^ i - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (Nat.one_le_pow i p (Fact.out : p.Prime).pos), Nat.cast_pow,
          Nat.cast_one]
      rw [hcast, Int.natAbs_natCast]
    · right
      rw [h]
      have hcast : (-((p : ℤ) ^ i) - 1) = -(((p ^ i + 1 : ℕ)) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one]; ring
      rw [hcast, Int.natAbs_neg, Int.natAbs_natCast]
  rcases hnat1 with h1 | h1
  · rw [h1] at hddef
    rw [← hddef] at harith1
    exact absurd harith1 (not_lt.mpr hOrb_bound)
  · rw [h1] at hddef
    rw [← hddef] at harith2
    exact absurd harith2 (not_lt.mpr hOrb_bound)

end Work.DSTR.M110
