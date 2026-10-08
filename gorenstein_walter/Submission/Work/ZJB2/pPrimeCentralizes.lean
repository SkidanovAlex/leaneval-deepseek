import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB.AutLemma
import Submission.Work.GLUE.PcoreApi
import Submission.Work.ZJB2.cbarNormalizes

/-!
# gorenstein_walter — `ZJB2.pPrimeCentralizes` (T52.53)

Glauberman 1968, proof of Theorem 5.2 (p. 1122): when `G = C_G(P)·S`, `P = O_p(G)`, `S ∈ Syl_p(G)`,
a `p'`-element `y` of `C_G(V̄)` (`V ≤ S`) centralizes `VP`.

The proof has two independent halves.

* **`memCentralizerOfMulEqTop`.**  `G = C_G(P)·S` forces `G/C_G(P)` to be a `p`-group (it is a
  quotient of `S`), so every `p'`-element of `G` lies in `C_G(P)`.  Formalised without quotients:
  write `y = c·s`; the automorphism `φ = MulAut.conjNormal` of `P` satisfies `φ y = φ s`, hence
  `orderOf (φ y) ∣ orderOf y` (a `p'`-number) and `orderOf (φ y) ∣ orderOf s ∣ p ^ k`
  (`s` lies in the `p`-group `S`), so `φ y = 1`, i.e. `s` — and then `y` — centralizes `P`.

* **`conjInvEqSelfOfCoprime`.**  If `y` centralizes `P`, acts trivially on `Q/P` (`y⁻¹x y x⁻¹ ∈ P`)
  and has order coprime to `|P|`, then `y` centralizes `Q`: put `h = y⁻¹xyx⁻¹ ∈ P`; then
  `(y⁻¹)^i x y^i = h^i x`, so `h^m = 1` for `m = orderOf y`, while `h^{|P|} = 1` by Lagrange and
  `(m, |P|) = 1`; hence `h = 1`.  (This is the paper's Lemma 5.3 computation, with the exponent
  `orderOf y` supplied by coprimality instead of `|P|`.)

For `y ∈ C_G(V̄)` and `x = q·v ∈ P ⊔ V` one then computes
`y⁻¹ qv y (qv)⁻¹ = (y⁻¹qy)·(v r v⁻¹)·q⁻¹ ∈ P` (where `y⁻¹vy = v r`, `r ∈ P`, comes from
`ZJB2.exists_mul_of_mem_cbar`), so `y` acts trivially on `(VP)/P`; the second half applies.
-/

namespace Work.ZJB2

open Subgroup
open Work.GW2

/-- **Coprime action trivial on the quotient.**  If `y` fixes a normal-enough subgroup `P` pointwise,
acts trivially on `Q/P` (`y⁻¹ * x * y * x⁻¹ ∈ P` for every `x ∈ Q`) and has order `m` coprime to
`|P|`, then `y` fixes `Q` pointwise. -/
theorem conjInvEqSelfOfCoprime {G : Type*} [Group G] {Q P : Subgroup G} {y : G} [Finite ↥P]
    (hfix : ∀ x ∈ P, y⁻¹ * x * y = x)
    (hquot : ∀ x ∈ Q, y⁻¹ * x * y * x⁻¹ ∈ P)
    {m : ℕ} (hy : y ^ m = 1) (hcop : Nat.Coprime m (Nat.card ↥P)) :
    ∀ x ∈ Q, y⁻¹ * x * y = x := by
  intro x hx
  set h : G := y⁻¹ * x * y * x⁻¹ with hh
  have hhP : h ∈ P := hquot x hx
  have hfixh : y⁻¹ * h * y = h := hfix h hhP
  have hxh : y⁻¹ * x * y = h * x := by rw [hh]; group
  have hfixpow : ∀ i : ℕ, y⁻¹ * h ^ i * y = h ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hstep : y⁻¹ * h ^ (i + 1) * y = (y⁻¹ * h ^ i * y) * (y⁻¹ * h * y) := by
        rw [pow_succ]; group
      rw [hstep, ih, hfixh, pow_succ]
  have key : ∀ i : ℕ, (y⁻¹) ^ i * x * y ^ i = h ^ i * x := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hstep : (y⁻¹) ^ (i + 1) * x * y ^ (i + 1) = y⁻¹ * ((y⁻¹) ^ i * x * y ^ i) * y := by
        rw [pow_succ', pow_succ']; group
      rw [hstep, ih]
      have hstep2 : y⁻¹ * (h ^ i * x) * y = (y⁻¹ * h ^ i * y) * (y⁻¹ * x * y) := by group
      rw [hstep2, hfixpow i, hxh, pow_succ]; group
  have hm : h ^ m = 1 := by
    have h0 := key m
    have h1 : (y⁻¹) ^ m = 1 := by rw [inv_pow, hy, inv_one]
    rw [h1, hy] at h0
    rw [one_mul, mul_one] at h0
    calc h ^ m = h ^ m * x * x⁻¹ := by group
      _ = x * x⁻¹ := by rw [← h0]
      _ = 1 := by group
  have hcard : h ^ Nat.card ↥P = 1 := by
    haveI : Fintype ↥P := Fintype.ofFinite ↥P
    have h1 : (⟨h, hhP⟩ : ↥P) ^ Fintype.card ↥P = 1 := pow_card_eq_one
    have h3 : P.subtype ((⟨h, hhP⟩ : ↥P) ^ Fintype.card ↥P)
        = h ^ Fintype.card ↥P := by
      rw [map_pow]; rfl
    rw [h1, map_one] at h3
    rw [Nat.card_eq_fintype_card]
    exact h3.symm
  have horder1 : orderOf h = 1 := by
    have hdvdm : orderOf h ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hm
    have hdvdP : orderOf h ∣ Nat.card ↥P := orderOf_dvd_iff_pow_eq_one.mpr hcard
    have hgcd : orderOf h ∣ Nat.gcd m (Nat.card ↥P) := Nat.dvd_gcd hdvdm hdvdP
    rw [hcop.gcd_eq_one] at hgcd
    exact Nat.dvd_one.mp hgcd
  have h1 : h = 1 := orderOf_eq_one_iff.mp horder1
  rw [hxh, h1, one_mul]

/-- **`p'`-elements of `G = C_G(P)·S` centralize `P`.**  `P ⊴ G`, `S ∈ Syl_p(G)`, every element of
`G` is a product of an element of `C_G(P)` and an element of `S`; then every element of `p'`-order
centralizes `P`. -/
theorem memCentralizerOfMulEqTop {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} [P.Normal] (S : Sylow p G)
    (hGCS : ∀ g : G, ∃ c ∈ Subgroup.centralizer (P : Set G),
      ∃ s ∈ (S : Subgroup G), g = c * s)
    {y : G} (hcop : (orderOf y).Coprime p) :
    y ∈ Subgroup.centralizer (P : Set G) := by
  obtain ⟨c, hc, s, hs, rfl⟩ := hGCS y
  have hc1 : MulAut.conjNormal (H := P) c = 1 := by
    ext z
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hcz : (z : G) * c = c * (z : G) := (Subgroup.mem_centralizer_iff.mp hc) (z : G) z.2
    rw [← hcz]; group
  have hφ : MulAut.conjNormal (H := P) (c * s) = MulAut.conjNormal (H := P) s := by
    rw [map_mul, hc1, one_mul]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' (⟨s, hs⟩ : ↥(S : Subgroup G))
  have hdvd : orderOf s ∣ p ^ k := by
    rw [← hk]
    exact orderOf_map_dvd (S : Subgroup G).subtype ⟨s, hs⟩
  have hdvdφ : orderOf (MulAut.conjNormal (H := P) (c * s)) ∣ p ^ k := by
    rw [hφ]
    exact dvd_trans (orderOf_map_dvd (MulAut.conjNormal (H := P)) s) hdvd
  have hgcd : orderOf (MulAut.conjNormal (H := P) (c * s)) ∣ 1 := by
    rw [← (hcop.pow_right k).gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_map_dvd (MulAut.conjNormal (H := P)) (c * s)) hdvdφ
  have h1 : MulAut.conjNormal (H := P) (c * s) = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have h2 : (MulAut.conjNormal (H := P) (c * s)) ⟨z, hz⟩ = ⟨z, hz⟩ := by
    rw [h1, MulAut.one_apply]
  have h3 : c * s * z * (c * s)⁻¹ = z := by
    have h4 := congrArg (fun w : ↥P => (w : G)) h2
    simpa only [MulAut.conjNormal_apply] using h4
  calc z * (c * s) = ((c * s) * z * (c * s)⁻¹) * (c * s) := by rw [h3]
    _ = (c * s) * z := by group

theorem pPrimeCentralizes (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Work.ZJB.PPrimeCentralizesProp p G := by
  intro S hGCS V hVS y hy hcop
  have hyP : y ∈ Subgroup.centralizer ((pCore p G : Subgroup G) : Set G) :=
    memCentralizerOfMulEqTop (P := (pCore p G : Subgroup G)) S hGCS hcop
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro x hx
  have hfix : ∀ z ∈ (pCore p G : Subgroup G), y⁻¹ * z * y = z := by
    intro z hz
    have hzy : z * y = y * z := (Subgroup.mem_centralizer_iff.mp hyP) z hz
    rw [mul_assoc, hzy]; group
  have hquot : ∀ z ∈ (V ⊔ pCore p G : Subgroup G),
      y⁻¹ * z * y * z⁻¹ ∈ pCore p G := by
    intro z hz
    have hz' : z ∈ (pCore p G ⊔ V : Subgroup G) := by
      rw [sup_comm]; exact hz
    obtain ⟨q, hq, v, hv, hqv⟩ := Subgroup.mem_sup_of_normal_left.mp hz'
    rw [← hqv]
    obtain ⟨r, hr, hyv⟩ := exists_mul_of_mem_cbar (pCore p G) V hy v hv
    have hqP : y⁻¹ * q * y ∈ pCore p G := by rw [hfix q hq]; exact hq
    have hvrP : v * r * v⁻¹ ∈ pCore p G := by
      have hh := Subgroup.Normal.conj_mem' (Work.GW2.pCore_normal p G) r hr v⁻¹
      simpa using hh
    have hcalc : y⁻¹ * (q * v) * y * (q * v)⁻¹
        = (y⁻¹ * q * y) * (v * r * v⁻¹) * q⁻¹ := by
      calc y⁻¹ * (q * v) * y * (q * v)⁻¹
          = (y⁻¹ * q * y) * (y⁻¹ * v * y) * (v⁻¹ * q⁻¹) := by group
        _ = (y⁻¹ * q * y) * (v * r) * (v⁻¹ * q⁻¹) := by rw [hyv]
        _ = (y⁻¹ * q * y) * (v * r * v⁻¹) * q⁻¹ := by group
    rw [hcalc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hqP hvrP) ((pCore p G).inv_mem hq)
  have hcopP : Nat.Coprime (orderOf y) (Nat.card ↥(pCore p G)) := by
    obtain ⟨k, hk⟩ := (Work.GW2.pCore_isPGroup (G := G) (p := p)).exists_card_eq
    rw [hk]
    exact hcop.pow_right k
  have hcomm := conjInvEqSelfOfCoprime (Q := (V ⊔ pCore p G : Subgroup G))
    (P := (pCore p G : Subgroup G)) hfix hquot (pow_orderOf_eq_one y) hcopP
  have hx' := hcomm x hx
  calc x * y = y * (y⁻¹ * x * y) := by group
    _ = y * x := by rw [hx']

end Work.ZJB2
