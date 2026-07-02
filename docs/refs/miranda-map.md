# Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5) — PDF navigation map

PDF file: `Algebraic Curves and Riemann Surfaces (Rick Miranda) (z-library.sk, 1lib.sk, z-lib.sk).pdf`
(399 PDF pages, image scan, **no OCR text layer** — use the `Read` tool with the `pages`
parameter; page numbers below in the "PDF" columns are exactly what `Read` expects.)

## Book page → PDF page offset rule

The offset is **not constant**: blank verso pages between some chapters were dropped
from the scan. Piecewise rule (`PDF = book + offset`):

| Book pages | Offset | Rule | Verified anchors (book = PDF) |
|---|---|---|---|
| i–viii (front matter) | — | not in scan (PDF 1–2 = title/copyright) | — |
| ix–xxi (roman: contents, preface) | −6 | PDF = roman − 6 | ix = 3, xviii = 12, xix = 13 |
| 1–55 | +15 | PDF = book + 15 | 1 = 16, 3 = 18, 20 = 35 |
| 57–127 (p. 56 blank, dropped) | +14 | PDF = book + 14 | 57 = 71, 104 = 118, 105 = 119 |
| 129–167 (p. 128 blank, dropped) | +13 | PDF = book + 13 | 129 = 142 |
| 169–321 (p. 168 blank, dropped) | +12 | PDF = book + 12 | 169 = 181, 172 = 184, 195 = 207, 246 = 258, 267 = 279, 269 = 281, 307 = 319, 309 = 321, 320 = 332 |
| 323–369 (p. 322 blank, dropped) | +11 | PDF = book + 11 | 323 = 334, 368 = 379 |
| 371–~389 (p. 370 blank, dropped) | +10 | PDF = book + 10 | 372 = 382, 378 = 388 |

## Chapter starts

| Chapter | Book | PDF |
|---|---|---|
| Contents | ix | 3 |
| Preface | xix | 13 |
| I. Riemann Surfaces: Basic Definitions | 1 | 16 |
| II. Functions and Maps | 21 | 36 |
| III. More Examples of Riemann Surfaces | 57 | 71 |
| IV. Integration on Riemann Surfaces | 105 | 119 |
| V. Divisors and Meromorphic Functions | 129 | 142 |
| VI. Algebraic Curves and the Riemann-Roch Theorem | 169 | 181 |
| VII. Applications of Riemann-Roch | 195 | 207 |
| VIII. Abel's Theorem | 247 | 259 |
| IX. Sheaves and Čech Cohomology | 269 | 281 |
| X. Algebraic Sheaves | 309 | 321 |
| XI. Invertible Sheaves, Line Bundles, and Ȟ¹ | 323 | 334 |
| References | 371 | 381 |
| Index of Notation | 377 | 387 |

## Section-level map (selected chapters)

### Ch. III (offset +14) — note: monodromy lives HERE, not in Ch. IV §1

| Section | Book | PDF |
|---|---|---|
| III.1 More Elementary Examples | 57 | 71 |
| III.2 Less Elementary Examples (plugging holes, nodes, cyclic coverings) | 66 | 80 |
| III.3 Group Actions on Riemann Surfaces | 75 | 89 |
| **III.4 Monodromy** (covering spaces & π₁ 84; monodromy of a finite covering 86; of a holomorphic map 87; coverings via monodromy representations 88; holomorphic maps via monodromy 90; maps to P¹ 91; hyperelliptic surfaces 92) | 84 | 98 |
| III.5 Basic Projective Geometry | 94 | 108 |

### Ch. IV Integration on Riemann Surfaces (offset +14)

**Caution:** Ch. IV §1 is *Differential Forms* — there is no monodromy/analytic
continuation here (that is Ch. III §4 above).

| Section | Book | PDF |
|---|---|---|
| IV.1 Differential Forms (holomorphic/meromorphic 1-forms, C∞ forms, types (1,0)/(0,1)) | 105 | 119 |
| IV.2 Operations on Differential Forms (Poincaré & Dolbeault lemmas 117) | 112 | 126 |
| IV.3 Integration on a Riemann Surface (residue of a meromorphic 1-form 121; Stokes 123; **Residue Theorem** 123; homotopy 124; homology 126) | 118 | 132 |

### Ch. V Divisors and Meromorphic Functions (offset +13)

| Section | Book | PDF |
|---|---|---|
| V.1 Divisors (definition 129; principal divisors 130; canonical divisors 131; deg K = 2g−2 context 132; ramification/branch divisors 134; partial ordering 136) | 129 | 142 |
| V.2 Linear Equivalence of Divisors | 138 | 151 |
| V.3 Spaces of Functions and Forms Associated to a Divisor — **L(D) defined** 145; complete linear systems \|D\| 147; L(D) isomorphisms under linear equivalence 148; **L⁽¹⁾(D) defined** 148; **isomorphism L⁽¹⁾(D) ≅ L(D+K)** (Lemma 3.11, used in Serre duality wrap-up) 149; L(D) for Riemann sphere 149; for complex torus 150; dimension bound 151 | 145 | 158 |
| V.4 Divisors and Maps to Projective Space (linear system of a map 155; base points 157; hyperplane divisor 158; φ_D embedding criteria 161) | 153 | 166 |

### Ch. VI Algebraic Curves and the Riemann-Roch Theorem (offset +12) — fine-grained

Chapter spans book 169–194 = **PDF 181–206**.

#### VI.1 Algebraic Curves (book 169 = PDF 181)

| Item | Book | PDF |
|---|---|---|
| Definition 1.1 (algebraic curve: M(X) separates points and tangents) | 169 | 181 |
| Examples 1.2–1.7 (sphere, torus, projective curves, hyperelliptic) | 170 | 182 |
| Example 1.8; **Theorem 1.9** (every compact Riemann surface is an algebraic curve — assumed) | 171 | 183 |
| Lemma 1.10 (function with ord_p(f) = N); Lemma 1.11 (prescribed Laurent tail at one point) | 171 | 183 |
| Lemma 1.12 (zero at p, pole at q); Lemma 1.13 (zero at p, poles at finitely many qᵢ) | 172 | 184 |
| Lemma 1.14 (high orders at finitely many points); **Lemma 1.15 (Laurent Series Approximation)**; Corollary 1.16 (prescribed orders) | 173 | 185 |
| Proposition 1.17 (M(X) finitely generated, trdeg = 1 over C) | 174 | 186 |
| Lemma 1.18; Corollary 1.19; Lemma 1.20 (dim L(mD) ≥ (m−m₀+1)k) | 175 | 187 |
| Proposition 1.21 ([M(X) : C(f)] = deg(div_∞(f))) | 176 | 188 |
| Proposition 1.22 (any separating field F = M(X)); Corollary 1.23 (function fields of standard examples) | 177 | 189 |
| Problems VI.1 | 178 | 190 |

#### VI.2 Laurent Tail Divisors (book 178 = PDF 190)

| Item | Book | PDF |
|---|---|---|
| Definition 2.1 (Laurent tail divisor; group T(X), subgroups T[D](X)); truncation maps t_{D₂}^{D₁}; multiplication operators μ_f; map α_D : M(X) → T[D](X) | 179 | 191 |
| Equation (2.2) (μ_f(α_D(g)) = α_{D−div(f)}(fg)); L(D) = ker(α_D) | 180 | 192 |
| Mittag-Leffler problems | 180–181 | 192–193 |
| **Definition of H¹(D) via Laurent tails: H¹(D) := coker(α_D) = T[D](X)/im(α_D)**; exact sequence 0 → M(X)/L(D) → T[D](X) → H¹(D) → 0 | 181 | 193 |
| "Comparing H¹ Spaces" (snake-lemma diagram) | 181 | 193 |
| **Lemma 2.3** (dim H¹(D₁/D₂) = [deg D₂ − dim L(D₂)] − [deg D₁ − dim L(D₁)]); long exact sequence remark | 182 | 194 |
| Finite-dimensionality subsection; Lemma 2.4 (dim H¹(0/mD) stabilizes) | 182 | 194 |
| Lemma 2.5 (deg A − dim L(A) uniformly bounded) | 183 | 195 |
| **Lemma 2.6** (for maximizing divisor A₀, H¹(A₀) = 0) | 184 | 196 |
| Proposition 2.7 (H¹(D) finite-dimensional for every D) | 184 | 196 |
| Problems VI.2 | 184–185 | 196–197 |

#### VI.3 The Riemann-Roch Theorem and Serre Duality (book 185 = PDF 197)

The blueprint's "pp. 186–188" = **PDF 198–200**.

| Item | Book | PDF |
|---|---|---|
| Section opens; splitting dim H¹(D₁/D₂) | 185 | 197 |
| **Theorem 3.1 (Riemann-Roch, First Form)**: dim L(D) − dim H¹(D) = deg(D) + 1 − dim H¹(0) | 186 | 198 |
| "The Residue Map" subsection begins; **equation (3.2): Σ_p Res_p(r_p ω) = 0** — the residue identity (note: it is a numbered *equation*, not "Lemma 3.2"; §3 has no Lemma 3.2) | 186 | 198 |
| Res_ω : T[D](X) → C defined; vanishes on im(α_D); descends to functional Res_ω : H¹(D) → C | 187 | 199 |
| Residue map Res : L⁽¹⁾(−D) → H¹(D)*; **Theorem 3.3 (Serre Duality)** stated: Res is an isomorphism, dim H¹(D) = dim L⁽¹⁾(−D) = dim L(K−D); proof of injectivity | 188 | 200 |
| Lemma 3.4 (two functionals agree after pullback by μ_{f₁}, μ_{f₂}); inequality (3.5) | 189 | 201 |
| **Lemma 3.6** (if Res_ω vanishes on ker t : T[D₁] → T[D₂] then ω ∈ L⁽¹⁾(−D₂)); Res_ω ∘ μ_f = Res_{fω}; **proof of surjectivity of Res begins** | 190 | 202 |
| Surjectivity proof concluded; dim L⁽¹⁾(−D) = dim L(K−D) via Lemma 3.11 of Ch. V — completes Serre duality; "The Equality of the Three Genera": (3.7) deg K = 2g−2, (3.8) dim H¹(K) = 1, (3.9), **(3.10) dim H¹(0) = dim L⁽¹⁾(0) = dim L(K) = g** | 191 | 203 |
| Three genera equal (topological = arithmetic = analytic); **Theorem 3.11 (Riemann-Roch, Second Form)**: dim L(D) − dim L(K−D) = deg(D) + 1 − g; Corollary 3.12 (deg D ≥ 2g−1 ⟹ H¹(D) = 0) | 192 | 204 |
| Problems VI.3; Further Reading | 193–194 | 205–206 |

### Ch. IX Sheaves and Čech Cohomology (offset +12)

| Section | Book | PDF |
|---|---|---|
| IX.1 Presheaves and Sheaves | 269 | 281 |
| IX.2 Sheaf Maps (exponential map 281; short exact sequences 284) | 278 | 290 |
| **IX.3 Čech Cohomology of Sheaves** (cochains 291; cohomology w.r.t. a cover 292; refinements 293; Čech groups 295; connecting homomorphism 297; long exact sequence 298) | 290 | 302 |
| IX.4 Cohomology Computations (vanishing of Ȟ¹ for C∞ sheaves 302, skyscrapers 303; Ȟ²(X, O_X[D]) = 0 304; De Rham 305; Dolbeault 306) | 301 | 313 |

### Ch. X Algebraic Sheaves (offset +12)

| Section | Book | PDF |
|---|---|---|
| X.1 Algebraic Sheaves of Functions and Forms (Zariski topology 311) | 309 | 321 |
| **X.2 Zariski Cohomology** — vanishing of Ȟ¹(X_Zar, F) for constant sheaves 313; **interpretation of H¹(D)** (Laurent-tail H¹(D) as Ȟ¹ of an algebraic sheaf) 314; GAGA theorems 315; further computations 316; Zero Mean Theorem 317; the high road to Abel's theorem 319; Problems X.2 320 | 312 | 324 |

Note: the identity **dim H¹(0) = g** is proved in Ch. VI §3, eq. (3.10), book 191 =
PDF 203 (via Serre duality); Ch. X §2 (book 314 = PDF 326) reinterprets these H¹(D)
spaces as Zariski sheaf cohomology, and Problems X.2 (book 320 = PDF 332) revisit
dim Ω¹(X) = g cohomologically.

### Ch. XI Invertible Sheaves, Line Bundles, and Ȟ¹ (offset +11)

| Section | Book | PDF |
|---|---|---|
| XI.1 Invertible Sheaves | 323 | 334 |
| XI.2 Line Bundles | 331 | 342 |
| XI.3 Avatars of the Picard Group (divisors mod linear equivalence & cocycles 345; invertible sheaves mod isomorphism 348; line bundles mod isomorphism 351; **the Jacobian** 356) | 345 | 356 |
| XI.4 Ȟ¹ as a Classifying Space (first-order deformations 364) | 357 | 368 |

## Key-topic one-liners

- **Divisors and linear systems L(D):** Ch. V — divisors book 129 = PDF 142; L(D) defined book 145 = PDF 158; complete linear systems |D| book 147 = PDF 160; L⁽¹⁾(D) book 148 = PDF 161; maps to projective space via |D| book 153 = PDF 166.
- **Riemann-Roch statement and proof:** Ch. VI §3, book 185–192 = PDF 197–204 — First Form (Thm 3.1) book 186 = PDF 198; proof completed via Serre duality (Thm 3.3, book 188 = PDF 200); Second Form (Thm 3.11) book 192 = PDF 204.
- **Abel's theorem:** Ch. VIII, book 247–267 = PDF 259–279 — statement (§2) book 250 = PDF 262; trace operations & necessity (§3) book 251–256 = PDF 263–268; sufficiency (§4) book 257–262 = PDF 269–274; genus-one applications (§5) book 265 = PDF 277.
- **Jacobian and period lattice:** Ch. VIII §1 "Homology, Periods, and the Jacobian" book 247–249 = PDF 259–261 (periods of 1-forms 247; Jac(X) = C^g/periods 248); Abel-Jacobi map (§2) book 249 = PDF 261; Riemann's bilinear relations book 262 = PDF 274; Jacobian vs. Picard group book 263 = PDF 275; algebraic take: Ch. XI §3 "The Jacobian" book 356 = PDF 367.
- **Monodromy / analytic continuation-style material:** Ch. III §4, book 84–93 = PDF 98–107 (NOT Ch. IV §1, which is differential forms).
- **Residue theorem (used for eq. (3.2)):** Ch. IV §3, book 123 = PDF 137.
