import Mathlib
import Submission.Work.OROneRel.bandLineGraphDefs
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.OROneRel.coset_lev

/-!
# The coset graph of `(H, t)` is the line graph of the chain of conjugates of `H` in `ker φ`

This file proves `Work.OROneRel.cosetGraph_lineGraph_iso`.  The bijection is
`gH ↦ (φ g, (g * t ^ (-(φ g).toAdd)) · chainPiece … (φ g).toAdd)`, with inverse
`(m, n · chainPiece m) ↦ (n * t ^ m) H`.
-/

namespace Work.OROneRel

open GradedHNN

universe u

section Helpers

variable {G : Type u} [Group G]

/-! ## The level function and the normalized representative -/

/-- The `φ`-level of an element: `wt φ g = (φ g).toAdd`. -/
def wt (φ : G →* Multiplicative ℤ) (g : G) : ℤ := (φ g).toAdd

@[simp] lemma wt_one (φ : G →* Multiplicative ℤ) : wt φ (1 : G) = 0 := by simp [wt]

@[simp] lemma wt_mul (φ : G →* Multiplicative ℤ) (g g' : G) :
    wt φ (g * g') = wt φ g + wt φ g' := by
  simp [wt, map_mul, toAdd_mul]

@[simp] lemma wt_inv (φ : G →* Multiplicative ℤ) (g : G) : wt φ g⁻¹ = -wt φ g := by
  simp [wt, map_inv, toAdd_inv]

@[simp] lemma wt_zpow (φ : G →* Multiplicative ℤ) (g : G) (m : ℤ) :
    wt φ (g ^ m) = m * wt φ g := by
  simp [wt, map_zpow, toAdd_zpow]

lemma wt_t (φ : G →* Multiplicative ℤ) (t : G) (ht : φ t = Multiplicative.ofAdd 1) :
    wt φ t = 1 := by
  simp [wt, ht]

lemma wt_t_pow (φ : G →* Multiplicative ℤ) (t : G) (ht : φ t = Multiplicative.ofAdd 1)
    (m : ℤ) : wt φ (t ^ m) = m := by rw [wt_zpow, wt_t φ t ht, mul_one]

lemma wt_mul_t (φ : G →* Multiplicative ℤ) (t : G) (ht : φ t = Multiplicative.ofAdd 1) (g : G) :
    wt φ (g * t) = wt φ g + 1 := by rw [wt_mul, wt_t φ t ht]

lemma wt_ker (φ : G →* Multiplicative ℤ) {g : G} (hg : g ∈ φ.ker) : wt φ g = 0 := by
  simp [wt, MonoidHom.mem_ker.mp hg]

lemma wt_eq_of_ker (φ : G →* Multiplicative ℤ) {a b : G} (hab : a⁻¹ * b ∈ φ.ker) :
    wt φ a = wt φ b := by
  have h : φ (a⁻¹ * b) = 1 := MonoidHom.mem_ker.mp hab
  rw [map_mul, map_inv] at h
  have h2 : φ b = φ a := by
    calc φ b = φ a * ((φ a)⁻¹ * φ b) := by group
      _ = φ a * 1 := by rw [h]
      _ = φ a := by rw [mul_one]
  simp [wt, h2.symm]

/-- The canonical `ker φ`-representative of the coset of `g`: `g * t ^ (-(wt φ g))`. -/
def nrm (φ : G →* Multiplicative ℤ) (t : G) (ht : φ t = Multiplicative.ofAdd 1) (g : G) :
    φ.ker :=
  ⟨g * t ^ (-(wt φ g)), by
    rw [MonoidHom.mem_ker]
    have hg : φ g = Multiplicative.ofAdd (wt φ g) := (ofAdd_toAdd (φ g)).symm
    rw [map_mul, map_zpow, ht, ← ofAdd_zsmul, smul_eq_mul, mul_one, hg, ← ofAdd_add,
      add_neg_cancel, ofAdd_zero]⟩

@[simp] lemma nrm_coe (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (g : G) :
    ((nrm φ t ht g : φ.ker) : G) = g * t ^ (-(wt φ g)) := rfl

lemma nrm_coe_mul_t (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (g : G) :
    ((nrm φ t ht (g * t) : φ.ker) : G) = ((nrm φ t ht g : φ.ker) : G) := by
  rw [nrm_coe, nrm_coe, wt_mul_t φ t ht g]
  rw [show -(wt φ g + 1) = -1 + -(wt φ g) by ring, zpow_add]
  group

lemma nrm_mul_t (φ : G →* Multiplicative ℤ) (t : G) (ht : φ t = Multiplicative.ofAdd 1)
    (g : G) : nrm φ t ht (g * t) = nrm φ t ht g :=
  Subtype.ext (nrm_coe_mul_t φ t ht g)

/-! ## Membership in the pieces of the chain -/

/-- The conjugation automorphism, applied. -/
lemma conjHom_apply (g h : G) : (↑(MulAut.conj g) : G →* G) h = g * h * g⁻¹ := rfl

lemma exists_mul_eq_of_mem_map_conj (H : Subgroup G) (t : G) (m : ℤ) {x : G}
    (hx : x ∈ H.map (MulAut.conj (t ^ m))) : ∃ h ∈ H, t ^ m * h = x * t ^ m := by
  obtain ⟨h, hh, heq⟩ := Subgroup.mem_map.mp hx
  refine ⟨h, hh, ?_⟩
  rw [← heq, conjHom_apply]
  group

lemma mem_conj_iff (H : Subgroup G) (t : G) (m : ℤ) {x : G} :
    x ∈ H.map (MulAut.conj (t ^ m)) ↔ t ^ (-m) * x * t ^ m ∈ H := by
  constructor
  · intro hx
    obtain ⟨h, hh, heq⟩ := Subgroup.mem_map.mp hx
    rw [← heq, conjHom_apply]
    convert hh using 1
    group
  · intro hx
    refine Subgroup.mem_map.mpr ⟨t ^ (-m) * x * t ^ m, hx, ?_⟩
    rw [conjHom_apply]
    group

lemma mem_chainPiece_iff (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker)
    (t : G) (m : ℤ) (n : φ.ker) :
    n ∈ chainPiece H t φ hH m ↔ (n : G) ∈ H.map (MulAut.conj (t ^ m)) := by
  rw [chainPiece, Subgroup.mem_subgroupOf]

/-! ## The bijection on vertices -/

/-- The vertex map on elements: `g ↦ (wt φ g, g t ^ (-(wt φ g)) · chainPiece (wt φ g))`. -/
noncomputable def toLineFun (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker)
    (t : G) (ht : φ t = Multiplicative.ofAdd 1) (g : G) : lineVertex H t φ hH :=
  ⟨wt φ g, QuotientGroup.mk (s := chainPiece H t φ hH (wt φ g)) (nrm φ t ht g)⟩

lemma toLineFun_eq (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker)
    (t : G) (ht : φ t = Multiplicative.ofAdd 1) {a b : G} (hab : a⁻¹ * b ∈ H) :
    toLineFun H φ hH t ht a = toLineFun H φ hH t ht b := by
  have hker : a⁻¹ * b ∈ φ.ker := hH hab
  have hwt : wt φ a = wt φ b := wt_eq_of_ker φ hker
  rw [toLineFun, toLineFun, hwt]
  congr 1
  rw [QuotientGroup.eq, mem_chainPiece_iff, mem_conj_iff]
  convert hab using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, nrm_coe, hwt]
  group

lemma toLineFun_mul_t (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker)
    (t : G) (ht : φ t = Multiplicative.ofAdd 1) (g : G) :
    toLineFun H φ hH t ht (g * t) =
      ⟨wt φ g + 1,
        QuotientGroup.mk (s := chainPiece H t φ hH (wt φ g + 1)) (nrm φ t ht g)⟩ := by
  rw [toLineFun, wt_mul_t φ t ht g, nrm_mul_t φ t ht g]

/-- The vertex of the line graph attached to a coset. -/
noncomputable def toLine (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker)
    (t : G) (ht : φ t = Multiplicative.ofAdd 1) : Coset H t → lineVertex H t φ hH :=
  fun q => q.liftOn' (toLineFun H φ hH t ht)
    (fun _ _ hab => toLineFun_eq H φ hH t ht (QuotientGroup.leftRel_apply.mp hab))

lemma toLine_cmk (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker)
    (t : G) (ht : φ t = Multiplicative.ofAdd 1) (a : G) :
    toLine H φ hH t ht (cmk H t a) = toLineFun H φ hH t ht a := by
  rw [toLine, cmk, Quotient.liftOn'_mk]

/-- The coset attached to a vertex of the line graph. -/
noncomputable def toGFun (H : Subgroup G) (φ : G →* Multiplicative ℤ) (t : G) (m : ℤ)
    (n : φ.ker) : Coset H t :=
  cmk H t ((n : G) * t ^ m)

lemma toGFun_eq (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (t : G)
    (m : ℤ) {n n' : φ.ker} (hn : n⁻¹ * n' ∈ chainPiece H t φ hH m) :
    toGFun H φ t m n = toGFun H φ t m n' := by
  have hx : ((n : G)⁻¹ * (n' : G)) ∈ H.map (MulAut.conj (t ^ m)) := by
    rw [mem_chainPiece_iff] at hn
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hn
  obtain ⟨h₀, hh₀, heq⟩ := exists_mul_eq_of_mem_map_conj H t m hx
  have heq' : ((n : G)⁻¹ * (n' : G)) = t ^ m * h₀ * t ^ (-m) := by
    calc ((n : G)⁻¹ * (n' : G)) = ((n : G)⁻¹ * (n' : G) * t ^ m) * t ^ (-m) := by group
      _ = (t ^ m * h₀) * t ^ (-m) := by rw [← heq]
      _ = t ^ m * h₀ * t ^ (-m) := by rw [mul_assoc]
  rw [toGFun, toGFun, cmk_eq_iff]
  have hsplit : ((n : G) * t ^ m)⁻¹ * ((n' : G) * t ^ m) =
      t ^ (-m) * ((n : G)⁻¹ * (n' : G)) * t ^ m := by group
  rw [hsplit, heq']
  convert hh₀ using 1
  group

noncomputable def toG (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (t : G)
    (_ht : φ t = Multiplicative.ofAdd 1) : lineVertex H t φ hH → Coset H t :=
  fun v => v.2.liftOn' (fun n : φ.ker => toGFun H φ t v.1 n)
    (fun _ _ hn => toGFun_eq H φ hH t v.1 (QuotientGroup.leftRel_apply.mp hn))

lemma toG_mk (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (m : ℤ) (n : φ.ker) :
    toG H φ hH t ht ⟨m, QuotientGroup.mk (s := chainPiece H t φ hH m) n⟩ =
      cmk H t ((n : G) * t ^ m) := by
  rw [toG, Quotient.liftOn'_mk]
  rfl

/-! ## The two round trips -/

lemma toG_toLine (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (a : G) :
    toG H φ hH t ht (toLine H φ hH t ht (cmk H t a)) = cmk H t a := by
  rw [toLine_cmk, toLineFun, toG_mk, nrm_coe]
  rw [show a * t ^ (-(wt φ a)) * t ^ (wt φ a) = a from by
    rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]]

lemma toLine_toG (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (v : lineVertex H t φ hH) :
    toLine H φ hH t ht (toG H φ hH t ht v) = v := by
  obtain ⟨m, q⟩ := v
  refine Quotient.inductionOn q ?_
  intro n
  rw [toG_mk, toLine_cmk, toLineFun]
  have hnm : wt φ (n : G) = 0 := wt_ker φ n.2
  have hl : wt φ ((n : G) * t ^ m) = m := by rw [wt_mul, hnm, zero_add, wt_t_pow φ t ht]
  have hsub : nrm φ t ht ((n : G) * t ^ m) = n := by
    refine Subtype.ext ?_
    rw [nrm_coe, hl]
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hl, hsub]

/-! ## The graph structure -/

lemma lineAdj_toLine_mul (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker)
    (t : G) (ht : φ t = Multiplicative.ofAdd 1) (g : G) :
    lineAdj H t φ hH (toLine H φ hH t ht (cmk H t g))
      (toLine H φ hH t ht (cmk H t (g * t))) := by
  refine Or.inl ⟨wt φ g, nrm φ t ht g, ?_, ?_⟩
  · rw [toLine_cmk]; rfl
  · rw [toLine_cmk, toLineFun_mul_t]

lemma adjC_to_lineAdj (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) {x y : Coset H t} (h : adjC H t x y) :
    lineAdj H t φ hH (toLine H φ hH t ht x) (toLine H φ hH t ht y) := by
  obtain ⟨g, hg | hg⟩ := h
  · rw [hg.1, hg.2]
    exact lineAdj_toLine_mul H φ hH t ht g
  · rw [hg.1, hg.2]
    exact lineAdj_symm H t φ hH (lineAdj_toLine_mul H φ hH t ht g)

/-- **The core of the converse.**  Two vertices of the line graph that share the representative
`n` at the consecutive levels `m` and `m + 1` come from adjacent cosets. -/
lemma adjC_of_same_rep (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) {a b : G} {m : ℤ} {n : φ.ker}
    (h1 : toLineFun H φ hH t ht a = ⟨m, QuotientGroup.mk (s := chainPiece H t φ hH m) n⟩)
    (h2 : toLineFun H φ hH t ht b =
      ⟨m + 1, QuotientGroup.mk (s := chainPiece H t φ hH (m + 1)) n⟩) :
    adjC H t (cmk H t a) (cmk H t b) := by
  -- levels and quotient components
  have hla : wt φ a = m := congrArg Sigma.fst h1
  have hq1 : QuotientGroup.mk (s := chainPiece H t φ hH m) (nrm φ t ht a) =
      QuotientGroup.mk (s := chainPiece H t φ hH m) n := by
    have h1' : (⟨m, QuotientGroup.mk (s := chainPiece H t φ hH m) (nrm φ t ht a)⟩ :
        lineVertex H t φ hH) =
        ⟨m, QuotientGroup.mk (s := chainPiece H t φ hH m) n⟩ := by
      rw [toLineFun] at h1
      rw [hla] at h1
      exact h1
    exact eq_of_heq (Sigma.ext_iff.mp h1').2
  have hlb : wt φ b = m + 1 := congrArg Sigma.fst h2
  have hq2 : QuotientGroup.mk (s := chainPiece H t φ hH (m + 1)) (nrm φ t ht b) =
      QuotientGroup.mk (s := chainPiece H t φ hH (m + 1)) n := by
    have h2' : (⟨m + 1, QuotientGroup.mk (s := chainPiece H t φ hH (m + 1))
        (nrm φ t ht b)⟩ : lineVertex H t φ hH) =
        ⟨m + 1, QuotientGroup.mk (s := chainPiece H t φ hH (m + 1)) n⟩ := by
      rw [toLineFun] at h2
      rw [hlb] at h2
      exact h2
    exact eq_of_heq (Sigma.ext_iff.mp h2').2
  -- from the level `m` piece
  have hna : n⁻¹ * nrm φ t ht a ∈ chainPiece H t φ hH m := by
    rw [← QuotientGroup.eq]
    exact hq1.symm
  have hxa : ((n : G)⁻¹ * (nrm φ t ht a : G)) ∈ H.map (MulAut.conj (t ^ m)) := by
    rw [mem_chainPiece_iff] at hna
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hna
  obtain ⟨h₁, hh₁, heq₁⟩ := exists_mul_eq_of_mem_map_conj H t m hxa
  -- `t ^ m * h₁ = n⁻¹ * a`
  have ha : t ^ m * h₁ = (n : G)⁻¹ * a := by
    have hx' : ((n : G)⁻¹ * (nrm φ t ht a : G)) * t ^ m = (n : G)⁻¹ * a := by
      rw [nrm_coe, hla]
      group
    rw [hx'] at heq₁
    exact heq₁
  have hca : ((n : G) * t ^ m)⁻¹ * a ∈ H := by
    have : ((n : G) * t ^ m)⁻¹ * a = h₁ := by
      calc ((n : G) * t ^ m)⁻¹ * a = t ^ (-m) * ((n : G)⁻¹ * a) := by group
        _ = t ^ (-m) * (t ^ m * h₁) := by rw [← ha]
        _ = h₁ := by group
    rw [this]; exact hh₁
  -- from the level `m + 1` piece
  have hnb : n⁻¹ * nrm φ t ht b ∈ chainPiece H t φ hH (m + 1) := by
    rw [← QuotientGroup.eq]
    exact hq2.symm
  have hxb : ((n : G)⁻¹ * (nrm φ t ht b : G)) ∈ H.map (MulAut.conj (t ^ (m + 1))) := by
    rw [mem_chainPiece_iff] at hnb
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hnb
  obtain ⟨h₂, hh₂, heq₂⟩ := exists_mul_eq_of_mem_map_conj H t (m + 1) hxb
  have hb : t ^ (m + 1) * h₂ = (n : G)⁻¹ * b := by
    have hx' : ((n : G)⁻¹ * (nrm φ t ht b : G)) * t ^ (m + 1) = (n : G)⁻¹ * b := by
      rw [nrm_coe, hlb]
      group
    rw [hx'] at heq₂
    exact heq₂
  have hcb : ((n : G) * t ^ (m + 1))⁻¹ * b ∈ H := by
    have : ((n : G) * t ^ (m + 1))⁻¹ * b = h₂ := by
      calc ((n : G) * t ^ (m + 1))⁻¹ * b = t ^ (-(m + 1)) * ((n : G)⁻¹ * b) := by group
        _ = t ^ (-(m + 1)) * (t ^ (m + 1) * h₂) := by rw [← hb]
        _ = h₂ := by group
    rw [this]; exact hh₂
  refine ⟨(n : G) * t ^ m, Or.inl ⟨?_, ?_⟩⟩
  · exact ((cmk_eq_iff H t).mpr hca).symm
  · rw [show (n : G) * t ^ m * t = (n : G) * t ^ (m + 1) by rw [mul_assoc, ← zpow_add_one]]
    exact ((cmk_eq_iff H t).mpr hcb).symm

lemma adjC_of_lineAdj_fun (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) {a b : G}
    (h : lineAdj H t φ hH (toLineFun H φ hH t ht a) (toLineFun H φ hH t ht b)) :
    adjC H t (cmk H t a) (cmk H t b) := by
  rcases h with ⟨m, n, h1, h2⟩ | ⟨m, n, h1, h2⟩
  · exact adjC_of_same_rep H φ hH t ht h1 h2
  · exact adjC_symm H t (adjC_of_same_rep H φ hH t ht h1 h2)

lemma lineAdj_to_adjC (H : Subgroup G) (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) {x y : Coset H t}
    (h : lineAdj H t φ hH (toLine H φ hH t ht x) (toLine H φ hH t ht y)) :
    adjC H t x y := by
  revert h
  refine Quotient.inductionOn x ?_
  intro a
  refine Quotient.inductionOn y ?_
  intro b h
  rw [toLine_cmk, toLine_cmk] at h
  exact adjC_of_lineAdj_fun H φ hH t ht h

end Helpers

/-- **The coset graph of a pair `(H, t)` is the line graph of the chain of conjugates of `H` in `ker φ`.**

`GradedHNN.Coset H t` is the left-coset space `G ⧸ H` with the (undirected) adjacency `adjC H t` joining `gH` and `gtH`; `lineVertex H t φ hH = Σ m : ℤ, (φ.ker ⧸ chainPiece H t φ hH m)` with `chainPiece … m = (t ^ m * H * t ^ (-m)).subgroupOf φ.ker`, and `lineAdj` joins two vertices when one is at level `m`, the other at level `m + 1` and the two cosets meet in `φ.ker`.

The isomorphism is `gH ↦ (φ g, (g * t ^ (-(φ g).toAdd)) · chainPiece … (φ g).toAdd)`; for the edge `{gH, gτH}` the two images have the *same* representative `g * t ^ (-(φ g).toAdd) ∈ ker φ` at the consecutive levels, which is exactly `lineAdj`. -/
theorem cosetGraph_lineGraph_iso {G : Type u} [Group G] (H : Subgroup G) (t : G)
    (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (ht : φ t = Multiplicative.ofAdd 1) :
    ∃ e : Work.OROneRel.GradedHNN.Coset H t ≃ Work.OROneRel.lineVertex H t φ hH,
      ∀ x y : Work.OROneRel.GradedHNN.Coset H t,
        Work.OROneRel.GradedHNN.adjC H t x y ↔ Work.OROneRel.lineAdj H t φ hH (e x) (e y) := by
  refine ⟨Equiv.mk (toLine H φ hH t ht) (toG H φ hH t ht) ?_ ?_, ?_⟩
  · intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact toG_toLine H φ hH t ht a
  · intro v
    exact toLine_toG H φ hH t ht v
  · intro x y
    show adjC H t x y ↔
      lineAdj H t φ hH (toLine H φ hH t ht x) (toLine H φ hH t ht y)
    exact ⟨adjC_to_lineAdj H φ hH t ht, lineAdj_to_adjC H φ hH t ht⟩

end Work.OROneRel
